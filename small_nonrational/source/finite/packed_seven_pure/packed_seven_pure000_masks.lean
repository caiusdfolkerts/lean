module
prelude
public import PackedSevenPure000Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenPure000
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

theorem maskTest_block_27 : Interval maskTest 864 896 :=
  interval_of_check maskTest 864 32 (by decide +kernel)

theorem maskTest_block_28 : Interval maskTest 896 928 :=
  interval_of_check maskTest 896 32 (by decide +kernel)

theorem maskTest_block_29 : Interval maskTest 928 960 :=
  interval_of_check maskTest 928 32 (by decide +kernel)

theorem maskTest_block_30 : Interval maskTest 960 992 :=
  interval_of_check maskTest 960 32 (by decide +kernel)

theorem maskTest_block_31 : Interval maskTest 992 1024 :=
  interval_of_check maskTest 992 32 (by decide +kernel)

theorem maskTest_block_32 : Interval maskTest 1024 1056 :=
  interval_of_check maskTest 1024 32 (by decide +kernel)

theorem maskTest_block_33 : Interval maskTest 1056 1088 :=
  interval_of_check maskTest 1056 32 (by decide +kernel)

theorem maskTest_block_34 : Interval maskTest 1088 1120 :=
  interval_of_check maskTest 1088 32 (by decide +kernel)

theorem maskTest_block_35 : Interval maskTest 1120 1144 :=
  interval_of_check maskTest 1120 24 (by decide +kernel)

theorem maskTest_complete : Interval maskTest 0 1144 :=
  (interval_append maskTest 0 576 1144
  (interval_append maskTest 0 288 576
  (interval_append maskTest 0 128 288
  (interval_append maskTest 0 64 128
  (interval_append maskTest 0 32 64
  maskTest_block_0
  maskTest_block_1)
  (interval_append maskTest 64 96 128
  maskTest_block_2
  maskTest_block_3))
  (interval_append maskTest 128 192 288
  (interval_append maskTest 128 160 192
  maskTest_block_4
  maskTest_block_5)
  (interval_append maskTest 192 224 288
  maskTest_block_6
  (interval_append maskTest 224 256 288
  maskTest_block_7
  maskTest_block_8))))
  (interval_append maskTest 288 416 576
  (interval_append maskTest 288 352 416
  (interval_append maskTest 288 320 352
  maskTest_block_9
  maskTest_block_10)
  (interval_append maskTest 352 384 416
  maskTest_block_11
  maskTest_block_12))
  (interval_append maskTest 416 480 576
  (interval_append maskTest 416 448 480
  maskTest_block_13
  maskTest_block_14)
  (interval_append maskTest 480 512 576
  maskTest_block_15
  (interval_append maskTest 512 544 576
  maskTest_block_16
  maskTest_block_17)))))
  (interval_append maskTest 576 864 1144
  (interval_append maskTest 576 704 864
  (interval_append maskTest 576 640 704
  (interval_append maskTest 576 608 640
  maskTest_block_18
  maskTest_block_19)
  (interval_append maskTest 640 672 704
  maskTest_block_20
  maskTest_block_21))
  (interval_append maskTest 704 768 864
  (interval_append maskTest 704 736 768
  maskTest_block_22
  maskTest_block_23)
  (interval_append maskTest 768 800 864
  maskTest_block_24
  (interval_append maskTest 800 832 864
  maskTest_block_25
  maskTest_block_26))))
  (interval_append maskTest 864 992 1144
  (interval_append maskTest 864 928 992
  (interval_append maskTest 864 896 928
  maskTest_block_27
  maskTest_block_28)
  (interval_append maskTest 928 960 992
  maskTest_block_29
  maskTest_block_30))
  (interval_append maskTest 992 1056 1144
  (interval_append maskTest 992 1024 1056
  maskTest_block_31
  maskTest_block_32)
  (interval_append maskTest 1056 1088 1144
  maskTest_block_33
  (interval_append maskTest 1088 1120 1144
  maskTest_block_34
  maskTest_block_35))))))

theorem selectedMasks_exact (i : Nat) : selectedMasks i = StreamingRawGrowth.nodeMask widths (codes i) := by
  by_cases hi : i < 1144
  · exact of_decide_eq_true (maskTest_complete i (Nat.zero_le _) hi)
  · simp only [selectedMasks, hi, ite_false]
theorem fastTest_sound (i : Nat) (h : fastTest i = true) : nodeTest i = true := by
  have checked := CachedMaskGrowth.countedCheck_sound widths 758 1024 1 1 1144
    candidateMasks badMasks kindMasks keys rawKind quota (fun _ c => c)
    rawLeaves codes counters selectedMasks (fun _ => rfl) selectedMasks_exact i h
  exact Bool.and_eq_true_iff.mpr checked
#print axioms fastTest_sound
end Papers.RationalityTen.PackedReplay.PackedSevenPure000
