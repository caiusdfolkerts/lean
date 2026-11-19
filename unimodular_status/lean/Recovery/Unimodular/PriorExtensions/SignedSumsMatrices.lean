/- Arbitrary-rank total-unimodularity of gluing along a compatible port.
The concrete port compatibility conditions are proved in SignedSumsPorts. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsPivot
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace Unimodular.SignedSums
open Pivot

variable {P T A B L R : Type*}

/-- Place the common ports above zero complementary coordinates. -/
def augment (C : Matrix P T ℤ) (U : Matrix (P ⊕ A) L ℤ) :
    Matrix (P ⊕ A) (T ⊕ L) ℤ :=
  fun i j => match j with
    | .inl t => match i with | .inl p => C p t | .inr _ => 0
    | .inr l => U i l

/-- The columns of the two summands in the actual glued coordinates. -/
def joined (U : Matrix (P ⊕ A) L ℤ) (V : Matrix (P ⊕ B) R ℤ) :
    Matrix (P ⊕ (A ⊕ B)) (L ⊕ R) ℤ :=
  fun i j => match i, j with
    | .inl p, .inl l => U (.inl p) l
    | .inl p, .inr r => V (.inl p) r
    | .inr (.inl a), .inl l => U (.inr a) l
    | .inr (.inl _), .inr _ => 0
    | .inr (.inr _), .inl _ => 0
    | .inr (.inr b), .inr r => V (.inr b) r

/-- A property of the port alone. The rank-one and triangle ports satisfy it. -/
def PortCompatible (C : Matrix P T ℤ) (L R : Type*) : Prop :=
  ∀ (U : Matrix P L ℤ) (V : Matrix P R ℤ),
    (Matrix.fromCols C U).IsTotallyUnimodular →
    (Matrix.fromCols C V).IsTotallyUnimodular →
    (Matrix.fromCols U V).IsTotallyUnimodular

theorem augment_head_tu (C : Matrix P T ℤ) (U : Matrix (P ⊕ A) L ℤ)
    (hU : (augment C U).IsTotallyUnimodular) :
    (Matrix.fromCols C (U.submatrix Sum.inl id)).IsTotallyUnimodular := by
  convert hU.submatrix Sum.inl id using 1
  ext p j
  cases j <;> rfl

theorem augment_eliminate [DecidableEq P] [DecidableEq A]
    (C : Matrix P T ℤ) (U : Matrix (P ⊕ A) L ℤ) (a : A) (l : L) :
    augment C (eliminate U (.inr a) l) =
      eliminate (augment C U) (.inr a) (.inr l) := by
  ext i j
  cases i <;> cases j <;> simp [augment, eliminate]

theorem joined_eliminate_left [DecidableEq P] [DecidableEq A] [DecidableEq B]
    (U : Matrix (P ⊕ A) L ℤ) (V : Matrix (P ⊕ B) R ℤ) (a : A) (l : L) :
    joined (eliminate U (.inr a) l) V =
      eliminate (joined U V) (.inr (.inl a)) (.inl l) := by
  ext i j
  cases i with
  | inl p => cases j <;> simp [joined, eliminate]
  | inr q => cases q <;> cases j <;> simp [joined, eliminate]

theorem joined_eliminate_right [DecidableEq P] [DecidableEq A] [DecidableEq B]
    (U : Matrix (P ⊕ A) L ℤ) (V : Matrix (P ⊕ B) R ℤ) (b : B) (r : R) :
    joined U (eliminate V (.inr b) r) =
      eliminate (joined U V) (.inr (.inr b)) (.inr r) := by
  ext i j
  cases i with
  | inl p => cases j <;> simp [joined, eliminate]
  | inr q => cases q <;> cases j <;> simp [joined, eliminate]

/-- Every minor of the glued matrix is small. Elimination is only at rows
outside the port, so the fixed port columns remain unchanged at every stage. -/
theorem joined_totallyUnimodular (C : Matrix P T ℤ)
    (hC : PortCompatible C L R)
    (U : Matrix (P ⊕ A) L ℤ) (V : Matrix (P ⊕ B) R ℤ)
    (hU : (augment C U).IsTotallyUnimodular)
    (hV : (augment C V).IsTotallyUnimodular) :
    (joined U V).IsTotallyUnimodular := by
  classical
  apply tu_of_small_det
  intro k
  induction k generalizing U V with
  | zero => intro f g; simp [Pivot.Small]
  | succ k ih =>
      intro f g
      by_cases hf : Function.Injective f
      · by_cases hport : ∀ i, ∃ p, f i = Sum.inl p
        · choose fp hfp using hport
          have ht := hC (U.submatrix Sum.inl id) (V.submatrix Sum.inl id)
            (augment_head_tu C U hU) (augment_head_tu C V hV)
          have hm : (joined U V).submatrix f g =
              (Matrix.fromCols (U.submatrix Sum.inl id) (V.submatrix Sum.inl id)).submatrix fp g := by
            ext i j
            simp only [Matrix.submatrix_apply]
            rw [hfp i]
            cases hgj : g j <;> simp [joined, hgj]
          rw [hm]
          exact small_det ht (k + 1) fp g
        · push_neg at hport
          obtain ⟨i, hi⟩ := hport
          cases hfi : f i with
          | inl p => exact False.elim (hi p hfi)
          | inr side =>
              by_cases hz : ∀ j, joined U V (f i) (g j) = 0
              · exact Or.inl (Matrix.det_eq_zero_of_row_eq_zero i hz)
              · push_neg at hz
                obtain ⟨j, hj⟩ := hz
                cases side with
                | inl a =>
                    cases hgj : g j with
                    | inr r => simp [hfi, hgj, joined] at hj
                    | inl l =>
                        have hne : U (.inr a) l ≠ 0 := by simpa [hfi, hgj, joined] using hj
                        have hp : Sign (U (.inr a) l) :=
                          sign_of_small_ne_zero (small_entry hU (.inr a) (.inr l)) hne
                        have hU' : (augment C (eliminate U (.inr a) l)).IsTotallyUnimodular := by
                          rw [augment_eliminate]
                          exact tu_eliminate hU (.inr a) (.inr l) hp
                        let W := joined (eliminate U (.inr a) l) V
                        have he : (W.submatrix f g).det = ((joined U V).submatrix f g).det := by
                          dsimp [W]
                          rw [joined_eliminate_left]
                          exact eliminate_det_of_row (joined U V) _ _ f g i hfi
                        rw [← he]
                        apply small_det_of_pivot (W.submatrix f g) i j
                        · intro q hqi
                          have hqr : f q ≠ Sum.inr (Sum.inl a) := by
                            intro hq
                            exact hqi (hf (hq.trans hfi.symm))
                          dsimp [W]
                          rw [joined_eliminate_left]
                          change eliminate (joined U V) (Sum.inr (Sum.inl a)) (Sum.inl l)
                            (f q) (g j) = 0
                          rw [hgj]
                          exact eliminate_pivot_column (joined U V) (Sum.inr (Sum.inl a))
                            (Sum.inl l) (by simpa [joined] using sign_square hp) (f q) hqr
                        · change Pivot.Small (joined (eliminate U (.inr a) l) V (f i) (g j))
                          simpa [hfi, hgj, joined, eliminate, augment] using
                            (small_entry hU (.inr a) (.inr l))
                        · simpa only [W, Matrix.submatrix_submatrix] using
                            ih (eliminate U (.inr a) l) V hU' hV
                              (f ∘ i.succAbove) (g ∘ j.succAbove)
                | inr b =>
                    cases hgj : g j with
                    | inl l => simp [hfi, hgj, joined] at hj
                    | inr r =>
                        have hne : V (.inr b) r ≠ 0 := by simpa [hfi, hgj, joined] using hj
                        have hp : Sign (V (.inr b) r) :=
                          sign_of_small_ne_zero (small_entry hV (.inr b) (.inr r)) hne
                        have hV' : (augment C (eliminate V (.inr b) r)).IsTotallyUnimodular := by
                          rw [augment_eliminate]
                          exact tu_eliminate hV (.inr b) (.inr r) hp
                        let W := joined U (eliminate V (.inr b) r)
                        have he : (W.submatrix f g).det = ((joined U V).submatrix f g).det := by
                          dsimp [W]
                          rw [joined_eliminate_right]
                          exact eliminate_det_of_row (joined U V) _ _ f g i hfi
                        rw [← he]
                        apply small_det_of_pivot (W.submatrix f g) i j
                        · intro q hqi
                          have hqr : f q ≠ Sum.inr (Sum.inr b) := by
                            intro hq
                            exact hqi (hf (hq.trans hfi.symm))
                          dsimp [W]
                          rw [joined_eliminate_right]
                          change eliminate (joined U V) (Sum.inr (Sum.inr b)) (Sum.inr r)
                            (f q) (g j) = 0
                          rw [hgj]
                          exact eliminate_pivot_column (joined U V) (Sum.inr (Sum.inr b))
                            (Sum.inr r) (by simpa [joined] using sign_square hp) (f q) hqr
                        · change Pivot.Small (joined U (eliminate V (.inr b) r) (f i) (g j))
                          simpa [hfi, hgj, joined, eliminate, augment] using
                            (small_entry hV (.inr b) (.inr r))
                        · simpa only [W, Matrix.submatrix_submatrix] using
                            ih U (eliminate V (.inr b) r) hU hV'
                              (f ∘ i.succAbove) (g ∘ j.succAbove)
      · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
        apply Or.inl
        apply Matrix.det_zero_of_row_eq (M := (joined U V).submatrix f g) hne
        funext q
        change joined U V (f i) (g q) = joined U V (f j) (g q)
        rw [hij]

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.joined_totallyUnimodular
