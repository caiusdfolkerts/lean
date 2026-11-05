module
prelude
public import PackedSevenMixed010Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed010
open Papers.RationalityTen Papers.RationalityTen.FiniteChecks
theorem maskTest_block_0 : Interval maskTest 0 32 :=
  interval_of_check maskTest 0 32 (by decide +kernel)

theorem maskTest_block_1 : Interval maskTest 32 64 :=
  interval_of_check maskTest 32 32 (by decide +kernel)

theorem maskTest_block_2 : Interval maskTest 64 96 :=
  interval_of_check maskTest 64 32 (by decide +kernel)

theorem maskTest_block_3 : Interval maskTest 96 128 :=
  interval_of_check maskTest 96 32 (by decide +kernel)

theorem maskTest_block_4 : Interval maskTest 128 160 :=
  interval_of_check maskTest 128 32 (by decide +kernel)

theorem maskTest_block_5 : Interval maskTest 160 192 :=
  interval_of_check maskTest 160 32 (by decide +kernel)

theorem maskTest_block_6 : Interval maskTest 192 196 :=
  interval_of_check maskTest 192 4 (by decide +kernel)

theorem maskTest_complete : Interval maskTest 0 196 :=
  (interval_append maskTest 0 96 196
  (interval_append maskTest 0 32 96
  maskTest_block_0
  (interval_append maskTest 32 64 96
  maskTest_block_1
  maskTest_block_2))
  (interval_append maskTest 96 160 196
  (interval_append maskTest 96 128 160
  maskTest_block_3
  maskTest_block_4)
  (interval_append maskTest 160 192 196
  maskTest_block_5
  maskTest_block_6)))

theorem selectedMasks_exact (i : Nat) : selectedMasks i = StreamingRawGrowth.nodeMask widths (codes i) := by
  by_cases hi : i < 196
  · exact of_decide_eq_true (maskTest_complete i (Nat.zero_le _) hi)
  · simp only [selectedMasks, hi, ite_false]
theorem fastTest_sound (i : Nat) (h : fastTest i = true) : nodeTest i = true := by
  have checked := CachedMaskGrowth.countedCheck_sound widths 430 1024 1 1 196
    candidateMasks badMasks kindMasks keys rawKind quota (fun _ c => c)
    rawLeaves codes counters selectedMasks (fun _ => rfl) selectedMasks_exact i h
  exact Bool.and_eq_true_iff.mpr checked
#print axioms fastTest_sound
end Papers.RationalityTen.PackedReplay.PackedSevenMixed010
