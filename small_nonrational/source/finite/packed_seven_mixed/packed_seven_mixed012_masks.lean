module
prelude
public import PackedSevenMixed012Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed012
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

theorem maskTest_block_12 : Interval maskTest 384 416 :=
  interval_of_check maskTest 384 32 (by decide +kernel)

theorem maskTest_block_13 : Interval maskTest 416 448 :=
  interval_of_check maskTest 416 32 (by decide +kernel)

theorem maskTest_block_14 : Interval maskTest 448 480 :=
  interval_of_check maskTest 448 32 (by decide +kernel)

theorem maskTest_block_15 : Interval maskTest 480 512 :=
  interval_of_check maskTest 480 32 (by decide +kernel)

theorem maskTest_block_16 : Interval maskTest 512 544 :=
  interval_of_check maskTest 512 32 (by decide +kernel)

theorem maskTest_block_17 : Interval maskTest 544 576 :=
  interval_of_check maskTest 544 32 (by decide +kernel)

theorem maskTest_block_18 : Interval maskTest 576 608 :=
  interval_of_check maskTest 576 32 (by decide +kernel)

theorem maskTest_block_19 : Interval maskTest 608 640 :=
  interval_of_check maskTest 608 32 (by decide +kernel)

theorem maskTest_block_20 : Interval maskTest 640 672 :=
  interval_of_check maskTest 640 32 (by decide +kernel)

theorem maskTest_block_21 : Interval maskTest 672 704 :=
  interval_of_check maskTest 672 32 (by decide +kernel)

theorem maskTest_block_22 : Interval maskTest 704 736 :=
  interval_of_check maskTest 704 32 (by decide +kernel)

theorem maskTest_block_23 : Interval maskTest 736 768 :=
  interval_of_check maskTest 736 32 (by decide +kernel)

theorem maskTest_block_24 : Interval maskTest 768 800 :=
  interval_of_check maskTest 768 32 (by decide +kernel)

theorem maskTest_block_25 : Interval maskTest 800 832 :=
  interval_of_check maskTest 800 32 (by decide +kernel)

theorem maskTest_block_26 : Interval maskTest 832 864 :=
  interval_of_check maskTest 832 32 (by decide +kernel)

theorem maskTest_block_27 : Interval maskTest 864 868 :=
  interval_of_check maskTest 864 4 (by decide +kernel)

theorem maskTest_complete : Interval maskTest 0 868 :=
  (interval_append maskTest 0 448 868
  (interval_append maskTest 0 224 448
  (interval_append maskTest 0 96 224
  (interval_append maskTest 0 32 96
  maskTest_block_0
  (interval_append maskTest 32 64 96
  maskTest_block_1
  maskTest_block_2))
  (interval_append maskTest 96 160 224
  (interval_append maskTest 96 128 160
  maskTest_block_3
  maskTest_block_4)
  (interval_append maskTest 160 192 224
  maskTest_block_5
  maskTest_block_6)))
  (interval_append maskTest 224 320 448
  (interval_append maskTest 224 256 320
  maskTest_block_7
  (interval_append maskTest 256 288 320
  maskTest_block_8
  maskTest_block_9))
  (interval_append maskTest 320 384 448
  (interval_append maskTest 320 352 384
  maskTest_block_10
  maskTest_block_11)
  (interval_append maskTest 384 416 448
  maskTest_block_12
  maskTest_block_13))))
  (interval_append maskTest 448 672 868
  (interval_append maskTest 448 544 672
  (interval_append maskTest 448 480 544
  maskTest_block_14
  (interval_append maskTest 480 512 544
  maskTest_block_15
  maskTest_block_16))
  (interval_append maskTest 544 608 672
  (interval_append maskTest 544 576 608
  maskTest_block_17
  maskTest_block_18)
  (interval_append maskTest 608 640 672
  maskTest_block_19
  maskTest_block_20)))
  (interval_append maskTest 672 768 868
  (interval_append maskTest 672 704 768
  maskTest_block_21
  (interval_append maskTest 704 736 768
  maskTest_block_22
  maskTest_block_23))
  (interval_append maskTest 768 832 868
  (interval_append maskTest 768 800 832
  maskTest_block_24
  maskTest_block_25)
  (interval_append maskTest 832 864 868
  maskTest_block_26
  maskTest_block_27)))))

theorem selectedMasks_exact (i : Nat) : selectedMasks i = StreamingRawGrowth.nodeMask widths (codes i) := by
  by_cases hi : i < 868
  · exact of_decide_eq_true (maskTest_complete i (Nat.zero_le _) hi)
  · simp only [selectedMasks, hi, ite_false]
theorem fastTest_sound (i : Nat) (h : fastTest i = true) : nodeTest i = true := by
  have checked := CachedMaskGrowth.countedCheck_sound widths 838 1024 1 1 868
    candidateMasks badMasks kindMasks keys rawKind quota (fun _ c => c)
    rawLeaves codes counters selectedMasks (fun _ => rfl) selectedMasks_exact i h
  exact Bool.and_eq_true_iff.mpr checked
#print axioms fastTest_sound
end Papers.RationalityTen.PackedReplay.PackedSevenMixed012
