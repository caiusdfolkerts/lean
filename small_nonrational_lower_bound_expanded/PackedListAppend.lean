module
prelude
public import PackedRawNatGrowth

@[expose] public section

namespace Papers.RationalityTen.PackedRawNatGrowth

/-- Exact composition of two decoder runs. This permits small certificates for
large literal support lists, without checking one large list equality. -/
theorem readList_add (width n m code : Nat) :
    readList width (n + m) code =
      let first := readList width n code
      let second := readList width m first.2
      (first.1 ++ second.1, second.2) := by
  induction n generalizing code with
  | zero => simp only [Nat.zero_add, readList, List.nil_append]
  | succ n ih =>
      simp only [Nat.succ_add, readList, ih, List.cons_append]

theorem readList_append_of_eq (width n m code rest finish : Nat)
    (first second : List Nat)
    (hfirst : readList width n code = (first, rest))
    (hsecond : readList width m rest = (second, finish)) :
    readList width (n + m) code = (first ++ second, finish) := by
  rw [readList_add, hfirst]
  dsimp only
  rw [hsecond]

end Papers.RationalityTen.PackedRawNatGrowth
