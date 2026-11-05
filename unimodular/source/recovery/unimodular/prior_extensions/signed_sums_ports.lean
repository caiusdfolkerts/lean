/- Exact port classifications for the signed one-, two-, and three-sums. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsMatrices
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums
open Pivot

theorem small_neg {a : ℤ} (ha : Pivot.Small a) : Pivot.Small (-a) := by
  rcases ha with rfl | rfl | rfl <;> norm_num [Pivot.Small]

theorem tu_one_row {J : Type*} (M : Matrix (Fin 1) J ℤ)
    (h : ∀ i j, Pivot.Small (M i j)) : M.IsTotallyUnimodular := by
  classical
  apply tu_of_small_det
  intro k f g
  cases k with
  | zero => simp [Pivot.Small]
  | succ k =>
      cases k with
      | zero => simpa using h (f 0) (g 0)
      | succ k =>
          have hni : ¬Function.Injective f := by
            intro hf
            have hc := Fintype.card_le_of_injective f hf
            simp only [Fintype.card_fin] at hc
            omega
          obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hni
          exact Or.inl (Matrix.det_zero_of_row_eq (M := M.submatrix f g) hne
            (by funext q; change M (f i) (g q) = M (f j) (g q); rw [hij]))

theorem tu_two_rows {J : Type*} (M : Matrix (Fin 2) J ℤ)
    (h : ∀ i j, Pivot.Small (M i j))
    (h₂ : ∀ r s j l, Pivot.Small (M r j * M s l - M r l * M s j)) :
    M.IsTotallyUnimodular := by
  classical
  apply tu_of_small_det
  intro k f g
  cases k with
  | zero => simp [Pivot.Small]
  | succ k =>
      cases k with
      | zero => simpa using h (f 0) (g 0)
      | succ k =>
          cases k with
          | zero =>
              simpa [Matrix.det_fin_two, Matrix.submatrix_apply] using
                (h₂ (f 0) (f 1) (g 0) (g 1))
          | succ k =>
              have hni : ¬Function.Injective f := by
                intro hf
                have hc := Fintype.card_le_of_injective f hf
                simp only [Fintype.card_fin] at hc
                omega
              obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hni
              exact Or.inl (Matrix.det_zero_of_row_eq (M := M.submatrix f g) hne
            (by funext q; change M (f i) (g q) = M (f j) (g q); rw [hij]))

/-- The triangle is the actual oriented circuit `a,b,a+b`. -/
def triangle : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 0, 1], ![0, 1, 1]]

def PortColumn (x y : ℤ) : Prop := Pivot.Small x ∧ Pivot.Small y ∧ Pivot.Small (x-y)

/-- Exact finite classification forced by the three port minors, with no
restriction on the number of complementary rows or other columns. -/
theorem portColumn_det {a b c d : ℤ} (hab : PortColumn a b) (hcd : PortColumn c d) :
    Pivot.Small (a*d-c*b) := by
  rcases hab with ⟨ha, hb, hab⟩
  rcases hcd with ⟨hc, hd, hcd⟩
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    rcases hd with rfl | rfl | rfl <;> norm_num [Pivot.Small] at *

theorem triangle_column {J : Type*} (U : Matrix (Fin 2) J ℤ)
    (hU : (Matrix.fromCols triangle U).IsTotallyUnimodular) (j : J) :
    PortColumn (U 0 j) (U 1 j) := by
  refine ⟨small_entry hU 0 (.inr j), small_entry hU 1 (.inr j), ?_⟩
  have hm := small_det hU 2 id ![Sum.inr j, Sum.inl 2]
  simpa [Matrix.det_fin_two, Matrix.submatrix_apply, triangle] using hm

theorem no_port_compatible {T L R : Type*} (C : Matrix (Fin 0) T ℤ) :
    PortCompatible C L R := by
  intro U V hU hV
  exact Matrix.emptyRows_isTotallyUnimodular _

theorem one_port_compatible {T L R : Type*} (C : Matrix (Fin 1) T ℤ) :
    PortCompatible C L R := by
  intro U V hU hV
  apply tu_one_row
  intro i j
  cases j with
  | inl l => exact small_entry hU i (.inr l)
  | inr r => exact small_entry hV i (.inr r)

theorem triangle_compatible {L R : Type*} : PortCompatible triangle L R := by
  intro U V hU hV
  have hc (j : L ⊕ R) : PortColumn (Matrix.fromCols U V 0 j)
      (Matrix.fromCols U V 1 j) := by
    cases j with
    | inl l => exact triangle_column U hU l
    | inr r => exact triangle_column V hV r
  apply tu_two_rows
  · intro i j
    fin_cases i
    · exact (hc j).1
    · exact (hc j).2.1
  · intro r s j l
    fin_cases r <;> fin_cases s
    · exact Or.inl (sub_eq_zero.mpr (mul_comm _ _))
    · exact portColumn_det (hc j) (hc l)
    · change Pivot.Small (Matrix.fromCols U V 1 j * Matrix.fromCols U V 0 l -
        Matrix.fromCols U V 1 l * Matrix.fromCols U V 0 j)
      have hh := small_neg (portColumn_det (hc j) (hc l))
      convert hh using 1 <;> ring
    · exact Or.inl (sub_eq_zero.mpr (mul_comm _ _))

/-- Matrix form of the full signed 3-sum, in arbitrary complementary ranks. -/
theorem triangle_sum_totallyUnimodular {A B L R : Type*}
    (U : Matrix (Fin 2 ⊕ A) L ℤ) (V : Matrix (Fin 2 ⊕ B) R ℤ)
    (hU : (augment triangle U).IsTotallyUnimodular)
    (hV : (augment triangle V).IsTotallyUnimodular) :
    (joined U V).IsTotallyUnimodular :=
  joined_totallyUnimodular triangle triangle_compatible U V hU hV

/-- Matrix form of the full signed 2-sum, in arbitrary complementary ranks. -/
theorem single_sum_totallyUnimodular {A B L R : Type*}
    (U : Matrix (Fin 1 ⊕ A) L ℤ) (V : Matrix (Fin 1 ⊕ B) R ℤ)
    (hU : (augment (1 : Matrix (Fin 1) (Fin 1) ℤ) U).IsTotallyUnimodular)
    (hV : (augment (1 : Matrix (Fin 1) (Fin 1) ℤ) V).IsTotallyUnimodular) :
    (joined U V).IsTotallyUnimodular :=
  joined_totallyUnimodular _ (one_port_compatible _) U V hU hV

/-- Matrix form of the 1-sum, with zero common port rank. -/
theorem direct_sum_totallyUnimodular {A B L R : Type*}
    (U : Matrix (Fin 0 ⊕ A) L ℤ) (V : Matrix (Fin 0 ⊕ B) R ℤ)
    (hU : (augment (0 : Matrix (Fin 0) (Fin 0) ℤ) U).IsTotallyUnimodular)
    (hV : (augment (0 : Matrix (Fin 0) (Fin 0) ℤ) V).IsTotallyUnimodular) :
    (joined U V).IsTotallyUnimodular :=
  joined_totallyUnimodular _ (no_port_compatible _) U V hU hV

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.triangle_compatible
#print axioms Unimodular.SignedSums.triangle_sum_totallyUnimodular
#print axioms Unimodular.SignedSums.single_sum_totallyUnimodular
#print axioms Unimodular.SignedSums.direct_sum_totallyUnimodular
