module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed012Data

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed012
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
cert_cellTest_block_2 0 0 8 8
cert_cellTest_block_2 1 8 16 8
cert_cellTest_block_2 2 16 24 8
cert_cellTest_block_2 3 24 32 8
cert_cellTest_block_2 4 32 40 8
cert_cellTest_block_2 5 40 48 8
cert_cellTest_block_2 6 48 56 8
cert_cellTest_block_2 7 56 64 8
cert_cellTest_block_2 8 64 72 8
cert_cellTest_block_2 9 72 80 8
cert_cellTest_block_2 10 80 88 8
cert_cellTest_block_2 11 88 96 8
cert_cellTest_block_2 12 96 104 8
cert_cellTest_block_2 13 104 112 8
cert_cellTest_block_2 14 112 120 8
cert_cellTest_block_2 15 120 128 8
cert_cellTest_block_2 16 128 136 8
cert_cellTest_block_2 17 136 144 8
cert_cellTest_block_2 18 144 152 8
cert_cellTest_block_2 19 152 160 8
cert_cellTest_block_2 20 160 168 8
cert_cellTest_block_2 21 168 176 8
cert_cellTest_block_2 22 176 184 8
cert_cellTest_block_2 23 184 192 8
cert_cellTest_block_2 24 192 200 8
cert_cellTest_block_2 25 200 208 8
cert_cellTest_block_2 26 208 216 8
cert_cellTest_block_2 27 216 224 8
cert_cellTest_block_2 28 224 232 8
cert_cellTest_block_2 29 232 240 8
cert_cellTest_block_2 30 240 248 8
cert_cellTest_block_2 31 248 256 8
cert_cellTest_block_2 32 256 264 8
cert_cellTest_block_2 33 264 272 8
cert_cellTest_block_2 34 272 280 8
cert_cellTest_block_2 35 280 288 8
cert_cellTest_block_2 36 288 296 8
cert_cellTest_block_2 37 296 304 8
cert_cellTest_block_2 38 304 312 8
cert_cellTest_block_2 39 312 320 8
cert_cellTest_block_2 40 320 328 8
cert_cellTest_block_2 41 328 336 8
cert_cellTest_block_2 42 336 344 8
cert_cellTest_block_2 43 344 352 8
cert_cellTest_block_2 44 352 360 8
cert_cellTest_block_2 45 360 368 8
cert_cellTest_block_2 46 368 376 8
cert_cellTest_block_2 47 376 384 8
cert_cellTest_block_2 48 384 392 8
cert_cellTest_block_2 49 392 400 8
cert_cellTest_block_2 50 400 408 8
cert_cellTest_block_2 51 408 416 8
cert_cellTest_block_2 52 416 424 8
cert_cellTest_block_2 53 424 432 8
cert_cellTest_block_2 54 432 440 8
cert_cellTest_block_2 55 440 448 8
cert_cellTest_block_2 56 448 456 8
cert_cellTest_block_2 57 456 464 8
cert_cellTest_block_2 58 464 472 8
cert_cellTest_block_2 59 472 480 8
cert_cellTest_block_2 60 480 488 8
cert_cellTest_block_2 61 488 496 8
cert_cellTest_block_2 62 496 504 8
cert_cellTest_block_2 63 504 512 8
cert_cellTest_block_2 64 512 520 8
cert_cellTest_block_2 65 520 528 8
cert_cellTest_block_2 66 528 536 8
cert_cellTest_block_2 67 536 544 8
cert_cellTest_block_2 68 544 552 8
cert_cellTest_block_2 69 552 560 8
cert_cellTest_block_2 70 560 568 8
cert_cellTest_block_2 71 568 576 8
cert_cellTest_block_2 72 576 584 8
cert_cellTest_block_2 73 584 592 8
cert_cellTest_block_2 74 592 600 8
cert_cellTest_block_2 75 600 608 8
cert_cellTest_block_2 76 608 616 8
cert_cellTest_block_2 77 616 624 8
cert_cellTest_block_2 78 624 632 8
cert_cellTest_block_2 79 632 640 8
cert_cellTest_block_2 80 640 648 8
cert_cellTest_block_2 81 648 656 8
cert_cellTest_block_2 82 656 664 8
cert_cellTest_block_2 83 664 672 8
cert_cellTest_block_2 84 672 680 8
cert_cellTest_block_2 85 680 688 8
cert_cellTest_block_2 86 688 696 8
cert_cellTest_block_2 87 696 704 8
cert_cellTest_block_2 88 704 712 8
cert_cellTest_block_2 89 712 720 8
cert_cellTest_block_2 90 720 728 8
cert_cellTest_block_2 91 728 736 8
cert_cellTest_block_2 92 736 744 8
cert_cellTest_block_2 93 744 752 8
cert_cellTest_block_2 94 752 760 8
cert_cellTest_block_2 95 760 768 8
cert_cellTest_block_2 96 768 776 8
cert_cellTest_block_2 97 776 784 8
cert_cellTest_block_2 98 784 792 8
cert_cellTest_block_2 99 792 800 8
cert_cellTest_block_2 100 800 808 8
cert_cellTest_block_2 101 808 816 8
cert_cellTest_block_2 102 816 824 8
cert_cellTest_block_2 103 824 832 8
cert_cellTest_block_2 104 832 838 6
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
