module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed009Data

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed009
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
cert_cellTest_block_2 104 832 840 8
cert_cellTest_block_2 105 840 848 8
cert_cellTest_block_2 106 848 856 8
cert_cellTest_block_2 107 856 864 8
cert_cellTest_block_2 108 864 872 8
cert_cellTest_block_2 109 872 880 8
cert_cellTest_block_2 110 880 888 8
cert_cellTest_block_2 111 888 896 8
cert_cellTest_block_2 112 896 904 8
cert_cellTest_block_2 113 904 910 6
theorem cellTest_complete : Interval cellTest 0 910 :=
  (interval_append cellTest 0 456 910
  (interval_append cellTest 0 224 456
  (interval_append cellTest 0 112 224
  (interval_append cellTest 0 56 112
  (interval_append cellTest 0 24 56
  (interval_append cellTest 0 8 24
  cellTest_block_0
  (interval_append cellTest 8 16 24
  cellTest_block_1
  cellTest_block_2))
  (interval_append cellTest 24 40 56
  (interval_append cellTest 24 32 40
  cellTest_block_3
  cellTest_block_4)
  (interval_append cellTest 40 48 56
  cellTest_block_5
  cellTest_block_6)))
  (interval_append cellTest 56 80 112
  (interval_append cellTest 56 64 80
  cellTest_block_7
  (interval_append cellTest 64 72 80
  cellTest_block_8
  cellTest_block_9))
  (interval_append cellTest 80 96 112
  (interval_append cellTest 80 88 96
  cellTest_block_10
  cellTest_block_11)
  (interval_append cellTest 96 104 112
  cellTest_block_12
  cellTest_block_13))))
  (interval_append cellTest 112 168 224
  (interval_append cellTest 112 136 168
  (interval_append cellTest 112 120 136
  cellTest_block_14
  (interval_append cellTest 120 128 136
  cellTest_block_15
  cellTest_block_16))
  (interval_append cellTest 136 152 168
  (interval_append cellTest 136 144 152
  cellTest_block_17
  cellTest_block_18)
  (interval_append cellTest 152 160 168
  cellTest_block_19
  cellTest_block_20)))
  (interval_append cellTest 168 192 224
  (interval_append cellTest 168 176 192
  cellTest_block_21
  (interval_append cellTest 176 184 192
  cellTest_block_22
  cellTest_block_23))
  (interval_append cellTest 192 208 224
  (interval_append cellTest 192 200 208
  cellTest_block_24
  cellTest_block_25)
  (interval_append cellTest 208 216 224
  cellTest_block_26
  cellTest_block_27)))))
  (interval_append cellTest 224 336 456
  (interval_append cellTest 224 280 336
  (interval_append cellTest 224 248 280
  (interval_append cellTest 224 232 248
  cellTest_block_28
  (interval_append cellTest 232 240 248
  cellTest_block_29
  cellTest_block_30))
  (interval_append cellTest 248 264 280
  (interval_append cellTest 248 256 264
  cellTest_block_31
  cellTest_block_32)
  (interval_append cellTest 264 272 280
  cellTest_block_33
  cellTest_block_34)))
  (interval_append cellTest 280 304 336
  (interval_append cellTest 280 288 304
  cellTest_block_35
  (interval_append cellTest 288 296 304
  cellTest_block_36
  cellTest_block_37))
  (interval_append cellTest 304 320 336
  (interval_append cellTest 304 312 320
  cellTest_block_38
  cellTest_block_39)
  (interval_append cellTest 320 328 336
  cellTest_block_40
  cellTest_block_41))))
  (interval_append cellTest 336 392 456
  (interval_append cellTest 336 360 392
  (interval_append cellTest 336 344 360
  cellTest_block_42
  (interval_append cellTest 344 352 360
  cellTest_block_43
  cellTest_block_44))
  (interval_append cellTest 360 376 392
  (interval_append cellTest 360 368 376
  cellTest_block_45
  cellTest_block_46)
  (interval_append cellTest 376 384 392
  cellTest_block_47
  cellTest_block_48)))
  (interval_append cellTest 392 424 456
  (interval_append cellTest 392 408 424
  (interval_append cellTest 392 400 408
  cellTest_block_49
  cellTest_block_50)
  (interval_append cellTest 408 416 424
  cellTest_block_51
  cellTest_block_52))
  (interval_append cellTest 424 440 456
  (interval_append cellTest 424 432 440
  cellTest_block_53
  cellTest_block_54)
  (interval_append cellTest 440 448 456
  cellTest_block_55
  cellTest_block_56))))))
  (interval_append cellTest 456 680 910
  (interval_append cellTest 456 568 680
  (interval_append cellTest 456 512 568
  (interval_append cellTest 456 480 512
  (interval_append cellTest 456 464 480
  cellTest_block_57
  (interval_append cellTest 464 472 480
  cellTest_block_58
  cellTest_block_59))
  (interval_append cellTest 480 496 512
  (interval_append cellTest 480 488 496
  cellTest_block_60
  cellTest_block_61)
  (interval_append cellTest 496 504 512
  cellTest_block_62
  cellTest_block_63)))
  (interval_append cellTest 512 536 568
  (interval_append cellTest 512 520 536
  cellTest_block_64
  (interval_append cellTest 520 528 536
  cellTest_block_65
  cellTest_block_66))
  (interval_append cellTest 536 552 568
  (interval_append cellTest 536 544 552
  cellTest_block_67
  cellTest_block_68)
  (interval_append cellTest 552 560 568
  cellTest_block_69
  cellTest_block_70))))
  (interval_append cellTest 568 624 680
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
  cellTest_block_77)))
  (interval_append cellTest 624 648 680
  (interval_append cellTest 624 632 648
  cellTest_block_78
  (interval_append cellTest 632 640 648
  cellTest_block_79
  cellTest_block_80))
  (interval_append cellTest 648 664 680
  (interval_append cellTest 648 656 664
  cellTest_block_81
  cellTest_block_82)
  (interval_append cellTest 664 672 680
  cellTest_block_83
  cellTest_block_84)))))
  (interval_append cellTest 680 792 910
  (interval_append cellTest 680 736 792
  (interval_append cellTest 680 704 736
  (interval_append cellTest 680 688 704
  cellTest_block_85
  (interval_append cellTest 688 696 704
  cellTest_block_86
  cellTest_block_87))
  (interval_append cellTest 704 720 736
  (interval_append cellTest 704 712 720
  cellTest_block_88
  cellTest_block_89)
  (interval_append cellTest 720 728 736
  cellTest_block_90
  cellTest_block_91)))
  (interval_append cellTest 736 760 792
  (interval_append cellTest 736 744 760
  cellTest_block_92
  (interval_append cellTest 744 752 760
  cellTest_block_93
  cellTest_block_94))
  (interval_append cellTest 760 776 792
  (interval_append cellTest 760 768 776
  cellTest_block_95
  cellTest_block_96)
  (interval_append cellTest 776 784 792
  cellTest_block_97
  cellTest_block_98))))
  (interval_append cellTest 792 848 910
  (interval_append cellTest 792 816 848
  (interval_append cellTest 792 800 816
  cellTest_block_99
  (interval_append cellTest 800 808 816
  cellTest_block_100
  cellTest_block_101))
  (interval_append cellTest 816 832 848
  (interval_append cellTest 816 824 832
  cellTest_block_102
  cellTest_block_103)
  (interval_append cellTest 832 840 848
  cellTest_block_104
  cellTest_block_105)))
  (interval_append cellTest 848 880 910
  (interval_append cellTest 848 864 880
  (interval_append cellTest 848 856 864
  cellTest_block_106
  cellTest_block_107)
  (interval_append cellTest 864 872 880
  cellTest_block_108
  cellTest_block_109))
  (interval_append cellTest 880 896 910
  (interval_append cellTest 880 888 896
  cellTest_block_110
  cellTest_block_111)
  (interval_append cellTest 896 904 910
  cellTest_block_112
  cellTest_block_113)))))))
end Papers.RationalityTen.PackedReplay.PackedSevenMixed009
