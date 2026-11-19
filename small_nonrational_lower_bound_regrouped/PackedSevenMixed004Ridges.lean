module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed004Data

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed004
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
cert_ridgeTest_block_2 0 0 16
cert_ridgeTest_block_2 1 16 32
cert_ridgeTest_block_2 2 32 48
cert_ridgeTest_block_2 3 48 64
cert_ridgeTest_block_2 4 64 80
cert_ridgeTest_block_2 5 80 96
cert_ridgeTest_block_2 6 96 112
cert_ridgeTest_block_2 7 112 128
cert_ridgeTest_block_2 8 128 144
cert_ridgeTest_block_2 9 144 160
cert_ridgeTest_block_2 10 160 176
cert_ridgeTest_block_2 11 176 192
cert_ridgeTest_block_2 12 192 208
cert_ridgeTest_block_2 13 208 224
cert_ridgeTest_block_2 14 224 240
cert_ridgeTest_block_2 15 240 256
cert_ridgeTest_block_2 16 256 272
cert_ridgeTest_block_2 17 272 288
cert_ridgeTest_block_2 18 288 304
cert_ridgeTest_block_2 19 304 320
cert_ridgeTest_block_2 20 320 336
cert_ridgeTest_block_2 21 336 352
cert_ridgeTest_block_2 22 352 368
cert_ridgeTest_block_2 23 368 384
cert_ridgeTest_block_2 24 384 400
cert_ridgeTest_block_2 25 400 416
cert_ridgeTest_block_2 26 416 432
cert_ridgeTest_block_2 27 432 448
cert_ridgeTest_block_2 28 448 464
cert_ridgeTest_block_2 29 464 480
cert_ridgeTest_block_2 30 480 496
cert_ridgeTest_block_2 31 496 512
cert_ridgeTest_block_2 32 512 528
cert_ridgeTest_block_2 33 528 544
cert_ridgeTest_block_2 34 544 560
cert_ridgeTest_block_2 35 560 576
cert_ridgeTest_block_2 36 576 592
cert_ridgeTest_block_2 37 592 608
cert_ridgeTest_block_2 38 608 624
cert_ridgeTest_block_2 39 624 640
cert_ridgeTest_block_2 40 640 656
cert_ridgeTest_block_2 41 656 672
cert_ridgeTest_block_2 42 672 688
cert_ridgeTest_block_2 43 688 704
cert_ridgeTest_block_2 44 704 720
cert_ridgeTest_block_2 45 720 736
cert_ridgeTest_block_2 46 736 752
cert_ridgeTest_block_2 47 752 768
cert_ridgeTest_block_2 48 768 784
cert_ridgeTest_block_2 49 784 800
cert_ridgeTest_block_2 50 800 816
cert_ridgeTest_block_2 51 816 832
cert_ridgeTest_block_2 52 832 848
cert_ridgeTest_block_2 53 848 864
cert_ridgeTest_block_2 54 864 880
cert_ridgeTest_block_2 55 880 896
cert_ridgeTest_block_2 56 896 912
cert_ridgeTest_block_2 57 912 928
cert_ridgeTest_block_2 58 928 944
cert_ridgeTest_block_2 59 944 960
cert_ridgeTest_block_2 60 960 976
cert_ridgeTest_block_2 61 976 992
cert_ridgeTest_block_2 62 992 1008
cert_ridgeTest_block_2 63 1008 1024
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
end Papers.RationalityTen.PackedReplay.PackedSevenMixed004
