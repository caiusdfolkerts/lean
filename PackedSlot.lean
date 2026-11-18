module
prelude
public import GraphPureGeometry
public import PackedGraphCertificate
public import Init.Data.Nat.Bitwise.Lemmas

@[expose] public section
namespace Papers.RationalityTen.ResidualBatch.TupleSharing
open GraphPureGeometry PackedGraphCertificate

/-- A bit of the i-th fixed-width slot equals the bit of its selected value.
The width hypothesis applies to every cell in the list. -/
theorem pack_bit {α : Type} (field : α → Nat) (w b : Nat) (hb : b < w) (xs : List α)
    (bounded : ∀ x ∈ xs, field x < 2^w) (i : Nat) (hi : i < xs.length) :
    (pack field w xs).testBit (w*i+b) = (field xs[i]).testBit b := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp [pack, Nat.testBit_shiftLeft, Nat.not_le_of_gt hb]
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      have hw : w ≤ w * (i+1) + b := by rw [Nat.mul_succ]; omega
      have hn : (field x).testBit (w*(i+1)+b) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (bounded x (by simp))
          (Nat.pow_le_pow_right (by decide : 0 < 2) hw))
      have shift : w * (i+1) + b - w = w*i+b := by rw [Nat.mul_succ]; omega
      simp only [pack, Nat.testBit_or, Nat.testBit_shiftLeft, hn, Bool.false_or,
        decide_eq_true hw, Bool.true_and, shift, List.getElem_cons_succ]
      exact ih (fun t ht => bounded t (List.mem_cons_of_mem _ ht)) i hi'

theorem get_pack {α : Type} (field : α → Nat) (w : Nat) (xs : List α)
    (bounded : ∀ x ∈ xs, field x < 2^w) (i : Nat) (hi : i < xs.length) :
    (Fields.mk w (pack field w xs)).get i = field xs[i] := by
  apply Nat.eq_of_testBit_eq
  intro b
  change (((pack field w xs >>> (w * i)) &&& ((1 <<< w) - 1)).testBit b) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hb : b < w
  · simpa [hb] using pack_bit field w b hb xs bounded i hi
  · have hlarge : w ≤ b := Nat.le_of_not_gt hb
    have hbound := bounded xs[i] (List.getElem_mem ..)
    have hz : (field xs[i]).testBit b = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hbound (Nat.pow_le_pow_right (by decide : 0 < 2) hlarge))
    simp [hb, hz]

end Papers.RationalityTen.ResidualBatch.TupleSharing
