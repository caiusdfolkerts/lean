module
prelude
public import PackedSevenMixed006Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed006
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

theorem maskTest_block_6 : Interval maskTest 192 224 :=
  interval_of_check maskTest 192 32 (by decide +kernel)

theorem maskTest_block_7 : Interval maskTest 224 256 :=
  interval_of_check maskTest 224 32 (by decide +kernel)

theorem maskTest_block_8 : Interval maskTest 256 288 :=
  interval_of_check maskTest 256 32 (by decide +kernel)

theorem maskTest_block_9 : Interval maskTest 288 320 :=
  interval_of_check maskTest 288 32 (by decide +kernel)

theorem maskTest_block_10 : Interval maskTest 320 352 :=
  interval_of_check maskTest 320 32 (by decide +kernel)

theorem maskTest_block_11 : Interval maskTest 352 384 :=
  interval_of_check maskTest 352 32 (by decide +kernel)

theorem maskTest_block_12 : Interval maskTest 384 397 :=
  interval_of_check maskTest 384 13 (by decide +kernel)

theorem maskTest_complete : Interval maskTest 0 397 :=
  (interval_append maskTest 0 192 397
  (interval_append maskTest 0 96 192
  (interval_append maskTest 0 32 96
  maskTest_block_0
  (interval_append maskTest 32 64 96
  maskTest_block_1
  maskTest_block_2))
  (interval_append maskTest 96 128 192
  maskTest_block_3
  (interval_append maskTest 128 160 192
  maskTest_block_4
  maskTest_block_5)))
  (interval_append maskTest 192 288 397
  (interval_append maskTest 192 224 288
  maskTest_block_6
  (interval_append maskTest 224 256 288
  maskTest_block_7
  maskTest_block_8))
  (interval_append maskTest 288 352 397
  (interval_append maskTest 288 320 352
  maskTest_block_9
  maskTest_block_10)
  (interval_append maskTest 352 384 397
  maskTest_block_11
  maskTest_block_12))))

theorem selectedMasks_exact (i : Nat) : selectedMasks i = StreamingRawGrowth.nodeMask widths (codes i) := by
  by_cases hi : i < 397
  · exact of_decide_eq_true (maskTest_complete i (Nat.zero_le _) hi)
  · simp only [selectedMasks, hi, ite_false]
theorem fastTest_sound (i : Nat) (h : fastTest i = true) : nodeTest i = true := by
  have checked := CachedMaskGrowth.countedCheck_sound widths 556 1024 1 1 397
    candidateMasks badMasks kindMasks keys rawKind quota (fun _ c => c)
    rawLeaves codes counters selectedMasks (fun _ => rfl) selectedMasks_exact i h
  exact Bool.and_eq_true_iff.mpr checked
#print axioms fastTest_sound
end Papers.RationalityTen.PackedReplay.PackedSevenMixed006
