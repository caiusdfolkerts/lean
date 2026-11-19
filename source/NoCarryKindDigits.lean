module
prelude
public import Init.Data.Bool
public import Init.Data.List.Lemmas
public import Init.Data.List.Nat.Sum
public import Init.Data.Nat.Lemmas
public import Init.Data.Nat.Div.Lemmas
public import Init.Omega

@[expose] public section

/-!
# Counting arbitrary natural-number kinds with base digits

Fewer than `base` summands cannot carry out of any digit. In particular,
there is no bound on the kinds occurring in the list. The proof removes
the zero kinds and divides the remaining powers by the base, then repeats
this argument at the desired digit.
-/

namespace Papers.RationalityTen.NoCarryKindDigits

universe u

theorem sum_powers_split {α : Type u} (base : Nat) (kind : α → Nat) (xs : List α) :
    (xs.map (fun x => base ^ kind x)).sum =
      (xs.filter (fun x => decide (kind x = 0))).length +
        base * ((xs.filter (fun x => decide (0 < kind x))).map
          (fun x => base ^ (kind x - 1))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hx : kind x with
    | zero =>
      simp [hx, ih, Nat.add_assoc, Nat.add_comm]
    | succ k =>
      simp [hx, ih, Nat.pow_succ, Nat.mul_add, Nat.mul_comm, Nat.add_left_comm]

theorem sum_powers_div {α : Type u} (base : Nat) (hbase : 0 < base)
    (kind : α → Nat) (xs : List α) (hxs : xs.length < base) :
    (xs.map (fun x => base ^ kind x)).sum / base =
      ((xs.filter (fun x => decide (0 < kind x))).map
        (fun x => base ^ (kind x - 1))).sum := by
  have hzero : (xs.filter (fun x => decide (kind x = 0))).length < base :=
    Nat.lt_of_le_of_lt (List.length_filter_le _ _) hxs
  rw [sum_powers_split, Nat.add_mul_div_left _ _ hbase,
    Nat.div_eq_of_lt hzero, Nat.zero_add]

theorem sum_powers_mod {α : Type u} (base : Nat)
    (kind : α → Nat) (xs : List α) (hxs : xs.length < base) :
    (xs.map (fun x => base ^ kind x)).sum % base =
      (xs.filter (fun x => decide (kind x = 0))).length := by
  have hzero : (xs.filter (fun x => decide (kind x = 0))).length < base :=
    Nat.lt_of_le_of_lt (List.length_filter_le _ _) hxs
  rw [sum_powers_split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hzero]

/-- Every base digit is exactly its kind count, with no finite kind bound. -/
theorem digit_eq_count {α : Type u} (base : Nat) (hbase : 2 ≤ base)
    (kind : α → Nat) (xs : List α) (hxs : xs.length < base) (key : Nat) :
    ((xs.map (fun x => base ^ kind x)).sum / base ^ key) % base =
      (xs.filter (fun x => decide (kind x = key))).length := by
  induction key generalizing xs kind with
  | zero =>
    simpa only [Nat.pow_zero, Nat.div_one] using sum_powers_mod base kind xs hxs
  | succ key ih =>
    rw [Nat.pow_succ, Nat.mul_comm (base ^ key) base,
      ← Nat.div_div_eq_div_mul, sum_powers_div base (by omega) kind xs hxs]
    have hfiltered : (xs.filter (fun x => decide (0 < kind x))).length < base :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) hxs
    rw [ih (fun x => kind x - 1) _ hfiltered]
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro x _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq]
    omega

end Papers.RationalityTen.NoCarryKindDigits
