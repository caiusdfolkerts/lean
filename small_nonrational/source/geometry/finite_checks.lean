module
prelude
public import PackedGrowthData
public import Init.Data.List.Nat.Range
public import Init.Data.Fin.Lemmas

@[expose] public section

/-! Pure Boolean interval checks avoid constructing large intermediate
`Decidable (∀ i : Fin n, ...)` proof objects during certificate replay. -/

namespace Papers.RationalityTen.FiniteChecks

def checkRange (test : Nat → Bool) (start count : Nat) : Bool :=
  (List.range' start count).all test

theorem checkRange_sound (test : Nat → Bool) (start count : Nat)
    (hcheck : checkRange test start count = true)
    (i : Nat) (hstart : start ≤ i) (hend : i < start + count) : test i = true :=
  List.all_eq_true.mp hcheck i (List.mem_range'_1.mpr ⟨hstart, hend⟩)

def Interval (test : Nat → Bool) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi → test i = true

theorem interval_of_check (test : Nat → Bool) (start count : Nat)
    (hcheck : checkRange test start count = true) : Interval test start (start + count) :=
  checkRange_sound test start count hcheck

theorem interval_append (test : Nat → Bool) (lo middle hi : Nat)
    (left : Interval test lo middle) (right : Interval test middle hi) :
    Interval test lo hi := by
  intro i hlo hhi
  by_cases hm : i < middle
  · exact left i hlo hm
  · exact right i (Nat.le_of_not_gt hm) hhi

theorem fin_of_interval {n : Nat} [NeZero n] (test : Fin n → Bool)
    (h : Interval (fun i => test (Fin.ofNat n i)) 0 n) : ∀ i, test i = true := by
  intro i
  have hi := h i.val (Nat.zero_le _) i.isLt
  simpa only [Fin.ofNat_val_eq_self] using hi

end Papers.RationalityTen.FiniteChecks
