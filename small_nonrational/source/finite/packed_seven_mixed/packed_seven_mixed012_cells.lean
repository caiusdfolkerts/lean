module
prelude
public import PackedSevenMixed012Data

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed012
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
theorem cellTest_block_0 : Interval cellTest 0 8 :=
  interval_of_check cellTest 0 8 (by decide +kernel)

theorem cellTest_block_1 : Interval cellTest 8 16 :=
  interval_of_check cellTest 8 8 (by decide +kernel)

theorem cellTest_block_2 : Interval cellTest 16 24 :=
  interval_of_check cellTest 16 8 (by decide +kernel)

theorem cellTest_block_3 : Interval cellTest 24 32 :=
  interval_of_check cellTest 24 8 (by decide +kernel)

theorem cellTest_block_4 : Interval cellTest 32 40 :=
  interval_of_check cellTest 32 8 (by decide +kernel)

theorem cellTest_block_5 : Interval cellTest 40 48 :=
  interval_of_check cellTest 40 8 (by decide +kernel)

theorem cellTest_block_6 : Interval cellTest 48 56 :=
  interval_of_check cellTest 48 8 (by decide +kernel)

theorem cellTest_block_7 : Interval cellTest 56 64 :=
  interval_of_check cellTest 56 8 (by decide +kernel)

theorem cellTest_block_8 : Interval cellTest 64 72 :=
  interval_of_check cellTest 64 8 (by decide +kernel)

theorem cellTest_block_9 : Interval cellTest 72 80 :=
  interval_of_check cellTest 72 8 (by decide +kernel)

theorem cellTest_block_10 : Interval cellTest 80 88 :=
  interval_of_check cellTest 80 8 (by decide +kernel)

theorem cellTest_block_11 : Interval cellTest 88 96 :=
  interval_of_check cellTest 88 8 (by decide +kernel)

theorem cellTest_block_12 : Interval cellTest 96 104 :=
  interval_of_check cellTest 96 8 (by decide +kernel)

theorem cellTest_block_13 : Interval cellTest 104 112 :=
  interval_of_check cellTest 104 8 (by decide +kernel)

theorem cellTest_block_14 : Interval cellTest 112 120 :=
  interval_of_check cellTest 112 8 (by decide +kernel)

theorem cellTest_block_15 : Interval cellTest 120 128 :=
  interval_of_check cellTest 120 8 (by decide +kernel)

theorem cellTest_block_16 : Interval cellTest 128 136 :=
  interval_of_check cellTest 128 8 (by decide +kernel)

theorem cellTest_block_17 : Interval cellTest 136 144 :=
  interval_of_check cellTest 136 8 (by decide +kernel)

theorem cellTest_block_18 : Interval cellTest 144 152 :=
  interval_of_check cellTest 144 8 (by decide +kernel)

theorem cellTest_block_19 : Interval cellTest 152 160 :=
  interval_of_check cellTest 152 8 (by decide +kernel)

theorem cellTest_block_20 : Interval cellTest 160 168 :=
  interval_of_check cellTest 160 8 (by decide +kernel)

theorem cellTest_block_21 : Interval cellTest 168 176 :=
  interval_of_check cellTest 168 8 (by decide +kernel)

theorem cellTest_block_22 : Interval cellTest 176 184 :=
  interval_of_check cellTest 176 8 (by decide +kernel)

theorem cellTest_block_23 : Interval cellTest 184 192 :=
  interval_of_check cellTest 184 8 (by decide +kernel)

theorem cellTest_block_24 : Interval cellTest 192 200 :=
  interval_of_check cellTest 192 8 (by decide +kernel)

theorem cellTest_block_25 : Interval cellTest 200 208 :=
  interval_of_check cellTest 200 8 (by decide +kernel)

theorem cellTest_block_26 : Interval cellTest 208 216 :=
  interval_of_check cellTest 208 8 (by decide +kernel)

theorem cellTest_block_27 : Interval cellTest 216 224 :=
  interval_of_check cellTest 216 8 (by decide +kernel)

theorem cellTest_block_28 : Interval cellTest 224 232 :=
  interval_of_check cellTest 224 8 (by decide +kernel)

theorem cellTest_block_29 : Interval cellTest 232 240 :=
  interval_of_check cellTest 232 8 (by decide +kernel)

theorem cellTest_block_30 : Interval cellTest 240 248 :=
  interval_of_check cellTest 240 8 (by decide +kernel)

theorem cellTest_block_31 : Interval cellTest 248 256 :=
  interval_of_check cellTest 248 8 (by decide +kernel)

theorem cellTest_block_32 : Interval cellTest 256 264 :=
  interval_of_check cellTest 256 8 (by decide +kernel)

theorem cellTest_block_33 : Interval cellTest 264 272 :=
  interval_of_check cellTest 264 8 (by decide +kernel)

theorem cellTest_block_34 : Interval cellTest 272 280 :=
  interval_of_check cellTest 272 8 (by decide +kernel)

theorem cellTest_block_35 : Interval cellTest 280 288 :=
  interval_of_check cellTest 280 8 (by decide +kernel)

theorem cellTest_block_36 : Interval cellTest 288 296 :=
  interval_of_check cellTest 288 8 (by decide +kernel)

theorem cellTest_block_37 : Interval cellTest 296 304 :=
  interval_of_check cellTest 296 8 (by decide +kernel)

theorem cellTest_block_38 : Interval cellTest 304 312 :=
  interval_of_check cellTest 304 8 (by decide +kernel)

theorem cellTest_block_39 : Interval cellTest 312 320 :=
  interval_of_check cellTest 312 8 (by decide +kernel)

theorem cellTest_block_40 : Interval cellTest 320 328 :=
  interval_of_check cellTest 320 8 (by decide +kernel)

theorem cellTest_block_41 : Interval cellTest 328 336 :=
  interval_of_check cellTest 328 8 (by decide +kernel)

theorem cellTest_block_42 : Interval cellTest 336 344 :=
  interval_of_check cellTest 336 8 (by decide +kernel)

theorem cellTest_block_43 : Interval cellTest 344 352 :=
  interval_of_check cellTest 344 8 (by decide +kernel)

theorem cellTest_block_44 : Interval cellTest 352 360 :=
  interval_of_check cellTest 352 8 (by decide +kernel)

theorem cellTest_block_45 : Interval cellTest 360 368 :=
  interval_of_check cellTest 360 8 (by decide +kernel)

theorem cellTest_block_46 : Interval cellTest 368 376 :=
  interval_of_check cellTest 368 8 (by decide +kernel)

theorem cellTest_block_47 : Interval cellTest 376 384 :=
  interval_of_check cellTest 376 8 (by decide +kernel)

theorem cellTest_block_48 : Interval cellTest 384 392 :=
  interval_of_check cellTest 384 8 (by decide +kernel)

theorem cellTest_block_49 : Interval cellTest 392 400 :=
  interval_of_check cellTest 392 8 (by decide +kernel)

theorem cellTest_block_50 : Interval cellTest 400 408 :=
  interval_of_check cellTest 400 8 (by decide +kernel)

theorem cellTest_block_51 : Interval cellTest 408 416 :=
  interval_of_check cellTest 408 8 (by decide +kernel)

theorem cellTest_block_52 : Interval cellTest 416 424 :=
  interval_of_check cellTest 416 8 (by decide +kernel)

theorem cellTest_block_53 : Interval cellTest 424 432 :=
  interval_of_check cellTest 424 8 (by decide +kernel)

theorem cellTest_block_54 : Interval cellTest 432 440 :=
  interval_of_check cellTest 432 8 (by decide +kernel)

theorem cellTest_block_55 : Interval cellTest 440 448 :=
  interval_of_check cellTest 440 8 (by decide +kernel)

theorem cellTest_block_56 : Interval cellTest 448 456 :=
  interval_of_check cellTest 448 8 (by decide +kernel)

theorem cellTest_block_57 : Interval cellTest 456 464 :=
  interval_of_check cellTest 456 8 (by decide +kernel)

theorem cellTest_block_58 : Interval cellTest 464 472 :=
  interval_of_check cellTest 464 8 (by decide +kernel)

theorem cellTest_block_59 : Interval cellTest 472 480 :=
  interval_of_check cellTest 472 8 (by decide +kernel)

theorem cellTest_block_60 : Interval cellTest 480 488 :=
  interval_of_check cellTest 480 8 (by decide +kernel)

theorem cellTest_block_61 : Interval cellTest 488 496 :=
  interval_of_check cellTest 488 8 (by decide +kernel)

theorem cellTest_block_62 : Interval cellTest 496 504 :=
  interval_of_check cellTest 496 8 (by decide +kernel)

theorem cellTest_block_63 : Interval cellTest 504 512 :=
  interval_of_check cellTest 504 8 (by decide +kernel)

theorem cellTest_block_64 : Interval cellTest 512 520 :=
  interval_of_check cellTest 512 8 (by decide +kernel)

theorem cellTest_block_65 : Interval cellTest 520 528 :=
  interval_of_check cellTest 520 8 (by decide +kernel)

theorem cellTest_block_66 : Interval cellTest 528 536 :=
  interval_of_check cellTest 528 8 (by decide +kernel)

theorem cellTest_block_67 : Interval cellTest 536 544 :=
  interval_of_check cellTest 536 8 (by decide +kernel)

theorem cellTest_block_68 : Interval cellTest 544 552 :=
  interval_of_check cellTest 544 8 (by decide +kernel)

theorem cellTest_block_69 : Interval cellTest 552 560 :=
  interval_of_check cellTest 552 8 (by decide +kernel)

theorem cellTest_block_70 : Interval cellTest 560 568 :=
  interval_of_check cellTest 560 8 (by decide +kernel)

theorem cellTest_block_71 : Interval cellTest 568 576 :=
  interval_of_check cellTest 568 8 (by decide +kernel)

theorem cellTest_block_72 : Interval cellTest 576 584 :=
  interval_of_check cellTest 576 8 (by decide +kernel)

theorem cellTest_block_73 : Interval cellTest 584 592 :=
  interval_of_check cellTest 584 8 (by decide +kernel)

theorem cellTest_block_74 : Interval cellTest 592 600 :=
  interval_of_check cellTest 592 8 (by decide +kernel)

theorem cellTest_block_75 : Interval cellTest 600 608 :=
  interval_of_check cellTest 600 8 (by decide +kernel)

theorem cellTest_block_76 : Interval cellTest 608 616 :=
  interval_of_check cellTest 608 8 (by decide +kernel)

theorem cellTest_block_77 : Interval cellTest 616 624 :=
  interval_of_check cellTest 616 8 (by decide +kernel)

theorem cellTest_block_78 : Interval cellTest 624 632 :=
  interval_of_check cellTest 624 8 (by decide +kernel)

theorem cellTest_block_79 : Interval cellTest 632 640 :=
  interval_of_check cellTest 632 8 (by decide +kernel)

theorem cellTest_block_80 : Interval cellTest 640 648 :=
  interval_of_check cellTest 640 8 (by decide +kernel)

theorem cellTest_block_81 : Interval cellTest 648 656 :=
  interval_of_check cellTest 648 8 (by decide +kernel)

theorem cellTest_block_82 : Interval cellTest 656 664 :=
  interval_of_check cellTest 656 8 (by decide +kernel)

theorem cellTest_block_83 : Interval cellTest 664 672 :=
  interval_of_check cellTest 664 8 (by decide +kernel)

theorem cellTest_block_84 : Interval cellTest 672 680 :=
  interval_of_check cellTest 672 8 (by decide +kernel)

theorem cellTest_block_85 : Interval cellTest 680 688 :=
  interval_of_check cellTest 680 8 (by decide +kernel)

theorem cellTest_block_86 : Interval cellTest 688 696 :=
  interval_of_check cellTest 688 8 (by decide +kernel)

theorem cellTest_block_87 : Interval cellTest 696 704 :=
  interval_of_check cellTest 696 8 (by decide +kernel)

theorem cellTest_block_88 : Interval cellTest 704 712 :=
  interval_of_check cellTest 704 8 (by decide +kernel)

theorem cellTest_block_89 : Interval cellTest 712 720 :=
  interval_of_check cellTest 712 8 (by decide +kernel)

theorem cellTest_block_90 : Interval cellTest 720 728 :=
  interval_of_check cellTest 720 8 (by decide +kernel)

theorem cellTest_block_91 : Interval cellTest 728 736 :=
  interval_of_check cellTest 728 8 (by decide +kernel)

theorem cellTest_block_92 : Interval cellTest 736 744 :=
  interval_of_check cellTest 736 8 (by decide +kernel)

theorem cellTest_block_93 : Interval cellTest 744 752 :=
  interval_of_check cellTest 744 8 (by decide +kernel)

theorem cellTest_block_94 : Interval cellTest 752 760 :=
  interval_of_check cellTest 752 8 (by decide +kernel)

theorem cellTest_block_95 : Interval cellTest 760 768 :=
  interval_of_check cellTest 760 8 (by decide +kernel)

theorem cellTest_block_96 : Interval cellTest 768 776 :=
  interval_of_check cellTest 768 8 (by decide +kernel)

theorem cellTest_block_97 : Interval cellTest 776 784 :=
  interval_of_check cellTest 776 8 (by decide +kernel)

theorem cellTest_block_98 : Interval cellTest 784 792 :=
  interval_of_check cellTest 784 8 (by decide +kernel)

theorem cellTest_block_99 : Interval cellTest 792 800 :=
  interval_of_check cellTest 792 8 (by decide +kernel)

theorem cellTest_block_100 : Interval cellTest 800 808 :=
  interval_of_check cellTest 800 8 (by decide +kernel)

theorem cellTest_block_101 : Interval cellTest 808 816 :=
  interval_of_check cellTest 808 8 (by decide +kernel)

theorem cellTest_block_102 : Interval cellTest 816 824 :=
  interval_of_check cellTest 816 8 (by decide +kernel)

theorem cellTest_block_103 : Interval cellTest 824 832 :=
  interval_of_check cellTest 824 8 (by decide +kernel)

theorem cellTest_block_104 : Interval cellTest 832 838 :=
  interval_of_check cellTest 832 6 (by decide +kernel)

theorem cellTest_complete : Interval cellTest 0 838 :=
  (interval_append cellTest 0 416 838
  (interval_append cellTest 0 208 416
  (interval_append cellTest 0 104 208
  (interval_append cellTest 0 48 104
  (interval_append cellTest 0 24 48
  (interval_append cellTest 0 8 24
  cellTest_block_0
  (interval_append cellTest 8 16 24
  cellTest_block_1
  cellTest_block_2))
  (interval_append cellTest 24 32 48
  cellTest_block_3
  (interval_append cellTest 32 40 48
  cellTest_block_4
  cellTest_block_5)))
  (interval_append cellTest 48 72 104
  (interval_append cellTest 48 56 72
  cellTest_block_6
  (interval_append cellTest 56 64 72
  cellTest_block_7
  cellTest_block_8))
  (interval_append cellTest 72 88 104
  (interval_append cellTest 72 80 88
  cellTest_block_9
  cellTest_block_10)
  (interval_append cellTest 88 96 104
  cellTest_block_11
  cellTest_block_12))))
  (interval_append cellTest 104 152 208
  (interval_append cellTest 104 128 152
  (interval_append cellTest 104 112 128
  cellTest_block_13
  (interval_append cellTest 112 120 128
  cellTest_block_14
  cellTest_block_15))
  (interval_append cellTest 128 136 152
  cellTest_block_16
  (interval_append cellTest 136 144 152
  cellTest_block_17
  cellTest_block_18)))
  (interval_append cellTest 152 176 208
  (interval_append cellTest 152 160 176
  cellTest_block_19
  (interval_append cellTest 160 168 176
  cellTest_block_20
  cellTest_block_21))
  (interval_append cellTest 176 192 208
  (interval_append cellTest 176 184 192
  cellTest_block_22
  cellTest_block_23)
  (interval_append cellTest 192 200 208
  cellTest_block_24
  cellTest_block_25)))))
  (interval_append cellTest 208 312 416
  (interval_append cellTest 208 256 312
  (interval_append cellTest 208 232 256
  (interval_append cellTest 208 216 232
  cellTest_block_26
  (interval_append cellTest 216 224 232
  cellTest_block_27
  cellTest_block_28))
  (interval_append cellTest 232 240 256
  cellTest_block_29
  (interval_append cellTest 240 248 256
  cellTest_block_30
  cellTest_block_31)))
  (interval_append cellTest 256 280 312
  (interval_append cellTest 256 264 280
  cellTest_block_32
  (interval_append cellTest 264 272 280
  cellTest_block_33
  cellTest_block_34))
  (interval_append cellTest 280 296 312
  (interval_append cellTest 280 288 296
  cellTest_block_35
  cellTest_block_36)
  (interval_append cellTest 296 304 312
  cellTest_block_37
  cellTest_block_38))))
  (interval_append cellTest 312 360 416
  (interval_append cellTest 312 336 360
  (interval_append cellTest 312 320 336
  cellTest_block_39
  (interval_append cellTest 320 328 336
  cellTest_block_40
  cellTest_block_41))
  (interval_append cellTest 336 344 360
  cellTest_block_42
  (interval_append cellTest 344 352 360
  cellTest_block_43
  cellTest_block_44)))
  (interval_append cellTest 360 384 416
  (interval_append cellTest 360 368 384
  cellTest_block_45
  (interval_append cellTest 368 376 384
  cellTest_block_46
  cellTest_block_47))
  (interval_append cellTest 384 400 416
  (interval_append cellTest 384 392 400
  cellTest_block_48
  cellTest_block_49)
  (interval_append cellTest 400 408 416
  cellTest_block_50
  cellTest_block_51))))))
  (interval_append cellTest 416 624 838
  (interval_append cellTest 416 520 624
  (interval_append cellTest 416 464 520
  (interval_append cellTest 416 440 464
  (interval_append cellTest 416 424 440
  cellTest_block_52
  (interval_append cellTest 424 432 440
  cellTest_block_53
  cellTest_block_54))
  (interval_append cellTest 440 448 464
  cellTest_block_55
  (interval_append cellTest 448 456 464
  cellTest_block_56
  cellTest_block_57)))
  (interval_append cellTest 464 488 520
  (interval_append cellTest 464 472 488
  cellTest_block_58
  (interval_append cellTest 472 480 488
  cellTest_block_59
  cellTest_block_60))
  (interval_append cellTest 488 504 520
  (interval_append cellTest 488 496 504
  cellTest_block_61
  cellTest_block_62)
  (interval_append cellTest 504 512 520
  cellTest_block_63
  cellTest_block_64))))
  (interval_append cellTest 520 568 624
  (interval_append cellTest 520 544 568
  (interval_append cellTest 520 528 544
  cellTest_block_65
  (interval_append cellTest 528 536 544
  cellTest_block_66
  cellTest_block_67))
  (interval_append cellTest 544 552 568
  cellTest_block_68
  (interval_append cellTest 552 560 568
  cellTest_block_69
  cellTest_block_70)))
  (interval_append cellTest 568 592 624
  (interval_append cellTest 568 576 592
  cellTest_block_71
  (interval_append cellTest 576 584 592
  cellTest_block_72
  cellTest_block_73))
  (interval_append cellTest 592 608 624
  (interval_append cellTest 592 600 608
  cellTest_block_74
  cellTest_block_75)
  (interval_append cellTest 608 616 624
  cellTest_block_76
  cellTest_block_77)))))
  (interval_append cellTest 624 728 838
  (interval_append cellTest 624 672 728
  (interval_append cellTest 624 648 672
  (interval_append cellTest 624 632 648
  cellTest_block_78
  (interval_append cellTest 632 640 648
  cellTest_block_79
  cellTest_block_80))
  (interval_append cellTest 648 656 672
  cellTest_block_81
  (interval_append cellTest 656 664 672
  cellTest_block_82
  cellTest_block_83)))
  (interval_append cellTest 672 696 728
  (interval_append cellTest 672 680 696
  cellTest_block_84
  (interval_append cellTest 680 688 696
  cellTest_block_85
  cellTest_block_86))
  (interval_append cellTest 696 712 728
  (interval_append cellTest 696 704 712
  cellTest_block_87
  cellTest_block_88)
  (interval_append cellTest 712 720 728
  cellTest_block_89
  cellTest_block_90))))
  (interval_append cellTest 728 784 838
  (interval_append cellTest 728 752 784
  (interval_append cellTest 728 736 752
  cellTest_block_91
  (interval_append cellTest 736 744 752
  cellTest_block_92
  cellTest_block_93))
  (interval_append cellTest 752 768 784
  (interval_append cellTest 752 760 768
  cellTest_block_94
  cellTest_block_95)
  (interval_append cellTest 768 776 784
  cellTest_block_96
  cellTest_block_97)))
  (interval_append cellTest 784 808 838
  (interval_append cellTest 784 792 808
  cellTest_block_98
  (interval_append cellTest 792 800 808
  cellTest_block_99
  cellTest_block_100))
  (interval_append cellTest 808 824 838
  (interval_append cellTest 808 816 824
  cellTest_block_101
  cellTest_block_102)
  (interval_append cellTest 824 832 838
  cellTest_block_103
  cellTest_block_104)))))))
end Papers.RationalityTen.PackedReplay.PackedSevenMixed012
