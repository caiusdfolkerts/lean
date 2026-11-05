module
prelude
public import PackedSevenMixed007Data

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed007
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
theorem ridgeTest_block_0 : Interval ridgeTest 0 16 :=
  interval_of_check ridgeTest 0 16 (by decide +kernel)

theorem ridgeTest_block_1 : Interval ridgeTest 16 32 :=
  interval_of_check ridgeTest 16 16 (by decide +kernel)

theorem ridgeTest_block_2 : Interval ridgeTest 32 48 :=
  interval_of_check ridgeTest 32 16 (by decide +kernel)

theorem ridgeTest_block_3 : Interval ridgeTest 48 64 :=
  interval_of_check ridgeTest 48 16 (by decide +kernel)

theorem ridgeTest_block_4 : Interval ridgeTest 64 80 :=
  interval_of_check ridgeTest 64 16 (by decide +kernel)

theorem ridgeTest_block_5 : Interval ridgeTest 80 96 :=
  interval_of_check ridgeTest 80 16 (by decide +kernel)

theorem ridgeTest_block_6 : Interval ridgeTest 96 112 :=
  interval_of_check ridgeTest 96 16 (by decide +kernel)

theorem ridgeTest_block_7 : Interval ridgeTest 112 128 :=
  interval_of_check ridgeTest 112 16 (by decide +kernel)

theorem ridgeTest_block_8 : Interval ridgeTest 128 144 :=
  interval_of_check ridgeTest 128 16 (by decide +kernel)

theorem ridgeTest_block_9 : Interval ridgeTest 144 160 :=
  interval_of_check ridgeTest 144 16 (by decide +kernel)

theorem ridgeTest_block_10 : Interval ridgeTest 160 176 :=
  interval_of_check ridgeTest 160 16 (by decide +kernel)

theorem ridgeTest_block_11 : Interval ridgeTest 176 192 :=
  interval_of_check ridgeTest 176 16 (by decide +kernel)

theorem ridgeTest_block_12 : Interval ridgeTest 192 208 :=
  interval_of_check ridgeTest 192 16 (by decide +kernel)

theorem ridgeTest_block_13 : Interval ridgeTest 208 224 :=
  interval_of_check ridgeTest 208 16 (by decide +kernel)

theorem ridgeTest_block_14 : Interval ridgeTest 224 240 :=
  interval_of_check ridgeTest 224 16 (by decide +kernel)

theorem ridgeTest_block_15 : Interval ridgeTest 240 256 :=
  interval_of_check ridgeTest 240 16 (by decide +kernel)

theorem ridgeTest_block_16 : Interval ridgeTest 256 272 :=
  interval_of_check ridgeTest 256 16 (by decide +kernel)

theorem ridgeTest_block_17 : Interval ridgeTest 272 288 :=
  interval_of_check ridgeTest 272 16 (by decide +kernel)

theorem ridgeTest_block_18 : Interval ridgeTest 288 304 :=
  interval_of_check ridgeTest 288 16 (by decide +kernel)

theorem ridgeTest_block_19 : Interval ridgeTest 304 320 :=
  interval_of_check ridgeTest 304 16 (by decide +kernel)

theorem ridgeTest_block_20 : Interval ridgeTest 320 336 :=
  interval_of_check ridgeTest 320 16 (by decide +kernel)

theorem ridgeTest_block_21 : Interval ridgeTest 336 352 :=
  interval_of_check ridgeTest 336 16 (by decide +kernel)

theorem ridgeTest_block_22 : Interval ridgeTest 352 368 :=
  interval_of_check ridgeTest 352 16 (by decide +kernel)

theorem ridgeTest_block_23 : Interval ridgeTest 368 384 :=
  interval_of_check ridgeTest 368 16 (by decide +kernel)

theorem ridgeTest_block_24 : Interval ridgeTest 384 400 :=
  interval_of_check ridgeTest 384 16 (by decide +kernel)

theorem ridgeTest_block_25 : Interval ridgeTest 400 416 :=
  interval_of_check ridgeTest 400 16 (by decide +kernel)

theorem ridgeTest_block_26 : Interval ridgeTest 416 432 :=
  interval_of_check ridgeTest 416 16 (by decide +kernel)

theorem ridgeTest_block_27 : Interval ridgeTest 432 448 :=
  interval_of_check ridgeTest 432 16 (by decide +kernel)

theorem ridgeTest_block_28 : Interval ridgeTest 448 464 :=
  interval_of_check ridgeTest 448 16 (by decide +kernel)

theorem ridgeTest_block_29 : Interval ridgeTest 464 480 :=
  interval_of_check ridgeTest 464 16 (by decide +kernel)

theorem ridgeTest_block_30 : Interval ridgeTest 480 496 :=
  interval_of_check ridgeTest 480 16 (by decide +kernel)

theorem ridgeTest_block_31 : Interval ridgeTest 496 512 :=
  interval_of_check ridgeTest 496 16 (by decide +kernel)

theorem ridgeTest_block_32 : Interval ridgeTest 512 528 :=
  interval_of_check ridgeTest 512 16 (by decide +kernel)

theorem ridgeTest_block_33 : Interval ridgeTest 528 544 :=
  interval_of_check ridgeTest 528 16 (by decide +kernel)

theorem ridgeTest_block_34 : Interval ridgeTest 544 560 :=
  interval_of_check ridgeTest 544 16 (by decide +kernel)

theorem ridgeTest_block_35 : Interval ridgeTest 560 576 :=
  interval_of_check ridgeTest 560 16 (by decide +kernel)

theorem ridgeTest_block_36 : Interval ridgeTest 576 592 :=
  interval_of_check ridgeTest 576 16 (by decide +kernel)

theorem ridgeTest_block_37 : Interval ridgeTest 592 608 :=
  interval_of_check ridgeTest 592 16 (by decide +kernel)

theorem ridgeTest_block_38 : Interval ridgeTest 608 624 :=
  interval_of_check ridgeTest 608 16 (by decide +kernel)

theorem ridgeTest_block_39 : Interval ridgeTest 624 640 :=
  interval_of_check ridgeTest 624 16 (by decide +kernel)

theorem ridgeTest_block_40 : Interval ridgeTest 640 656 :=
  interval_of_check ridgeTest 640 16 (by decide +kernel)

theorem ridgeTest_block_41 : Interval ridgeTest 656 672 :=
  interval_of_check ridgeTest 656 16 (by decide +kernel)

theorem ridgeTest_block_42 : Interval ridgeTest 672 688 :=
  interval_of_check ridgeTest 672 16 (by decide +kernel)

theorem ridgeTest_block_43 : Interval ridgeTest 688 704 :=
  interval_of_check ridgeTest 688 16 (by decide +kernel)

theorem ridgeTest_block_44 : Interval ridgeTest 704 720 :=
  interval_of_check ridgeTest 704 16 (by decide +kernel)

theorem ridgeTest_block_45 : Interval ridgeTest 720 736 :=
  interval_of_check ridgeTest 720 16 (by decide +kernel)

theorem ridgeTest_block_46 : Interval ridgeTest 736 752 :=
  interval_of_check ridgeTest 736 16 (by decide +kernel)

theorem ridgeTest_block_47 : Interval ridgeTest 752 768 :=
  interval_of_check ridgeTest 752 16 (by decide +kernel)

theorem ridgeTest_block_48 : Interval ridgeTest 768 784 :=
  interval_of_check ridgeTest 768 16 (by decide +kernel)

theorem ridgeTest_block_49 : Interval ridgeTest 784 800 :=
  interval_of_check ridgeTest 784 16 (by decide +kernel)

theorem ridgeTest_block_50 : Interval ridgeTest 800 816 :=
  interval_of_check ridgeTest 800 16 (by decide +kernel)

theorem ridgeTest_block_51 : Interval ridgeTest 816 832 :=
  interval_of_check ridgeTest 816 16 (by decide +kernel)

theorem ridgeTest_block_52 : Interval ridgeTest 832 848 :=
  interval_of_check ridgeTest 832 16 (by decide +kernel)

theorem ridgeTest_block_53 : Interval ridgeTest 848 864 :=
  interval_of_check ridgeTest 848 16 (by decide +kernel)

theorem ridgeTest_block_54 : Interval ridgeTest 864 880 :=
  interval_of_check ridgeTest 864 16 (by decide +kernel)

theorem ridgeTest_block_55 : Interval ridgeTest 880 896 :=
  interval_of_check ridgeTest 880 16 (by decide +kernel)

theorem ridgeTest_block_56 : Interval ridgeTest 896 912 :=
  interval_of_check ridgeTest 896 16 (by decide +kernel)

theorem ridgeTest_block_57 : Interval ridgeTest 912 928 :=
  interval_of_check ridgeTest 912 16 (by decide +kernel)

theorem ridgeTest_block_58 : Interval ridgeTest 928 944 :=
  interval_of_check ridgeTest 928 16 (by decide +kernel)

theorem ridgeTest_block_59 : Interval ridgeTest 944 960 :=
  interval_of_check ridgeTest 944 16 (by decide +kernel)

theorem ridgeTest_block_60 : Interval ridgeTest 960 976 :=
  interval_of_check ridgeTest 960 16 (by decide +kernel)

theorem ridgeTest_block_61 : Interval ridgeTest 976 992 :=
  interval_of_check ridgeTest 976 16 (by decide +kernel)

theorem ridgeTest_block_62 : Interval ridgeTest 992 1008 :=
  interval_of_check ridgeTest 992 16 (by decide +kernel)

theorem ridgeTest_block_63 : Interval ridgeTest 1008 1024 :=
  interval_of_check ridgeTest 1008 16 (by decide +kernel)

theorem ridgeTest_complete : Interval ridgeTest 0 1024 :=
  (interval_append ridgeTest 0 512 1024
  (interval_append ridgeTest 0 256 512
  (interval_append ridgeTest 0 128 256
  (interval_append ridgeTest 0 64 128
  (interval_append ridgeTest 0 32 64
  (interval_append ridgeTest 0 16 32
  ridgeTest_block_0
  ridgeTest_block_1)
  (interval_append ridgeTest 32 48 64
  ridgeTest_block_2
  ridgeTest_block_3))
  (interval_append ridgeTest 64 96 128
  (interval_append ridgeTest 64 80 96
  ridgeTest_block_4
  ridgeTest_block_5)
  (interval_append ridgeTest 96 112 128
  ridgeTest_block_6
  ridgeTest_block_7)))
  (interval_append ridgeTest 128 192 256
  (interval_append ridgeTest 128 160 192
  (interval_append ridgeTest 128 144 160
  ridgeTest_block_8
  ridgeTest_block_9)
  (interval_append ridgeTest 160 176 192
  ridgeTest_block_10
  ridgeTest_block_11))
  (interval_append ridgeTest 192 224 256
  (interval_append ridgeTest 192 208 224
  ridgeTest_block_12
  ridgeTest_block_13)
  (interval_append ridgeTest 224 240 256
  ridgeTest_block_14
  ridgeTest_block_15))))
  (interval_append ridgeTest 256 384 512
  (interval_append ridgeTest 256 320 384
  (interval_append ridgeTest 256 288 320
  (interval_append ridgeTest 256 272 288
  ridgeTest_block_16
  ridgeTest_block_17)
  (interval_append ridgeTest 288 304 320
  ridgeTest_block_18
  ridgeTest_block_19))
  (interval_append ridgeTest 320 352 384
  (interval_append ridgeTest 320 336 352
  ridgeTest_block_20
  ridgeTest_block_21)
  (interval_append ridgeTest 352 368 384
  ridgeTest_block_22
  ridgeTest_block_23)))
  (interval_append ridgeTest 384 448 512
  (interval_append ridgeTest 384 416 448
  (interval_append ridgeTest 384 400 416
  ridgeTest_block_24
  ridgeTest_block_25)
  (interval_append ridgeTest 416 432 448
  ridgeTest_block_26
  ridgeTest_block_27))
  (interval_append ridgeTest 448 480 512
  (interval_append ridgeTest 448 464 480
  ridgeTest_block_28
  ridgeTest_block_29)
  (interval_append ridgeTest 480 496 512
  ridgeTest_block_30
  ridgeTest_block_31)))))
  (interval_append ridgeTest 512 768 1024
  (interval_append ridgeTest 512 640 768
  (interval_append ridgeTest 512 576 640
  (interval_append ridgeTest 512 544 576
  (interval_append ridgeTest 512 528 544
  ridgeTest_block_32
  ridgeTest_block_33)
  (interval_append ridgeTest 544 560 576
  ridgeTest_block_34
  ridgeTest_block_35))
  (interval_append ridgeTest 576 608 640
  (interval_append ridgeTest 576 592 608
  ridgeTest_block_36
  ridgeTest_block_37)
  (interval_append ridgeTest 608 624 640
  ridgeTest_block_38
  ridgeTest_block_39)))
  (interval_append ridgeTest 640 704 768
  (interval_append ridgeTest 640 672 704
  (interval_append ridgeTest 640 656 672
  ridgeTest_block_40
  ridgeTest_block_41)
  (interval_append ridgeTest 672 688 704
  ridgeTest_block_42
  ridgeTest_block_43))
  (interval_append ridgeTest 704 736 768
  (interval_append ridgeTest 704 720 736
  ridgeTest_block_44
  ridgeTest_block_45)
  (interval_append ridgeTest 736 752 768
  ridgeTest_block_46
  ridgeTest_block_47))))
  (interval_append ridgeTest 768 896 1024
  (interval_append ridgeTest 768 832 896
  (interval_append ridgeTest 768 800 832
  (interval_append ridgeTest 768 784 800
  ridgeTest_block_48
  ridgeTest_block_49)
  (interval_append ridgeTest 800 816 832
  ridgeTest_block_50
  ridgeTest_block_51))
  (interval_append ridgeTest 832 864 896
  (interval_append ridgeTest 832 848 864
  ridgeTest_block_52
  ridgeTest_block_53)
  (interval_append ridgeTest 864 880 896
  ridgeTest_block_54
  ridgeTest_block_55)))
  (interval_append ridgeTest 896 960 1024
  (interval_append ridgeTest 896 928 960
  (interval_append ridgeTest 896 912 928
  ridgeTest_block_56
  ridgeTest_block_57)
  (interval_append ridgeTest 928 944 960
  ridgeTest_block_58
  ridgeTest_block_59))
  (interval_append ridgeTest 960 992 1024
  (interval_append ridgeTest 960 976 992
  ridgeTest_block_60
  ridgeTest_block_61)
  (interval_append ridgeTest 992 1008 1024
  ridgeTest_block_62
  ridgeTest_block_63))))))
end Papers.RationalityTen.PackedReplay.PackedSevenMixed007
