module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed031OutsideData
public import CachedCellRelabel

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed031.Outside.Verified
open Papers.RationalityTen ConcreteGrowth FiniteChecks RawGraphGrowthFrames
open Papers.RationalityTen.FacetUniverses.RootedSevenMixed031.Outside
cert_renameCodeTable
cert_renameCode
cert_maskTest_2 0
cert_maskTest_block_2 0 0 0 16
cert_maskTest_block_2 0 1 16 32
cert_maskTest_block_2 0 2 32 48
cert_maskTest_block_2 0 3 48 64
cert_maskTest_block_2 0 4 64 80
cert_maskTest_block_2 0 5 80 96
cert_maskTest_block_2 0 6 96 112
cert_maskTest_block_2 0 7 112 128
cert_maskTest_block_2 0 8 128 144
cert_maskTest_block_2 0 9 144 160
cert_maskTest_block_2 0 10 160 176
cert_maskTest_block_2 0 11 176 192
cert_maskTest_block_2 0 12 192 208
cert_maskTest_block_2 0 13 208 224
cert_maskTest_block_2 0 14 224 240
cert_maskTest_block_2 0 15 240 256
cert_maskTest_block_2 0 16 256 272
cert_maskTest_block_2 0 17 272 288
cert_maskTest_block_2 0 18 288 304
cert_maskTest_block_2 0 19 304 320
cert_maskTest_block_2 0 20 320 336
cert_maskTest_block_2 0 21 336 352
cert_maskTest_block_2 0 22 352 368
cert_maskTest_block_2 0 23 368 384
cert_maskTest_block_2 0 24 384 400
cert_maskTest_block_2 0 25 400 416
cert_maskTest_block_2 0 26 416 432
cert_maskTest_block_2 0 27 432 448
cert_maskTest_block_2 0 28 448 464
cert_maskTest_block_2 0 29 464 480
cert_maskTest_block_2 0 30 480 496
cert_maskTest_block_2 0 31 496 512
cert_maskTest_block_2 0 32 512 528
cert_maskTest_block_2 0 33 528 544
cert_maskTest_block_2 0 34 544 560
cert_maskTest_block_2 0 35 560 576
cert_maskTest_block_2 0 36 576 592
cert_maskTest_block_2 0 37 592 608
cert_maskTest_block_2 0 38 608 624
cert_maskTest_block_2 0 39 624 640
cert_maskTest_block_2 0 40 640 656
cert_maskTest_block_2 0 41 656 672
cert_maskTest_block_2 0 42 672 688
cert_maskTest_block_2 0 43 688 704
cert_maskTest_block_2 0 44 704 720
cert_maskTest_block_2 0 45 720 736
cert_maskTest_block_2 0 46 736 752
cert_maskTest_block_2 0 47 752 768
cert_maskTest_block_2 0 48 768 784
cert_maskTest_block_2 0 49 784 800
cert_maskTest_block_2 0 50 800 816
cert_maskTest_block_2 0 51 816 832
cert_maskTest_block_2 0 52 832 848
cert_maskTest_block_2 0 53 848 864
cert_maskTest_block_2 0 54 864 880
cert_maskTest_block_2 0 55 880 896
cert_maskTest_block_2 0 56 896 912
cert_maskTest_block_2 0 57 912 928
cert_maskTest_block_2 0 58 928 944
cert_maskTest_block_2 0 59 944 960
cert_maskTest_block_2 0 60 960 976
cert_maskTest_block_2 0 61 976 992
cert_maskTest_block_2 0 62 992 1008
cert_maskTest_block_2 0 63 1008 1024
theorem maskTest0_complete : Interval maskTest0 0 1024 :=
  (interval_append maskTest0 0 512 1024
  (interval_append maskTest0 0 256 512
  (interval_append maskTest0 0 128 256
  (interval_append maskTest0 0 64 128
  (interval_append maskTest0 0 32 64
  (interval_append maskTest0 0 16 32
  maskTest0_block_0
  maskTest0_block_1)
  (interval_append maskTest0 32 48 64
  maskTest0_block_2
  maskTest0_block_3))
  (interval_append maskTest0 64 96 128
  (interval_append maskTest0 64 80 96
  maskTest0_block_4
  maskTest0_block_5)
  (interval_append maskTest0 96 112 128
  maskTest0_block_6
  maskTest0_block_7)))
  (interval_append maskTest0 128 192 256
  (interval_append maskTest0 128 160 192
  (interval_append maskTest0 128 144 160
  maskTest0_block_8
  maskTest0_block_9)
  (interval_append maskTest0 160 176 192
  maskTest0_block_10
  maskTest0_block_11))
  (interval_append maskTest0 192 224 256
  (interval_append maskTest0 192 208 224
  maskTest0_block_12
  maskTest0_block_13)
  (interval_append maskTest0 224 240 256
  maskTest0_block_14
  maskTest0_block_15))))
  (interval_append maskTest0 256 384 512
  (interval_append maskTest0 256 320 384
  (interval_append maskTest0 256 288 320
  (interval_append maskTest0 256 272 288
  maskTest0_block_16
  maskTest0_block_17)
  (interval_append maskTest0 288 304 320
  maskTest0_block_18
  maskTest0_block_19))
  (interval_append maskTest0 320 352 384
  (interval_append maskTest0 320 336 352
  maskTest0_block_20
  maskTest0_block_21)
  (interval_append maskTest0 352 368 384
  maskTest0_block_22
  maskTest0_block_23)))
  (interval_append maskTest0 384 448 512
  (interval_append maskTest0 384 416 448
  (interval_append maskTest0 384 400 416
  maskTest0_block_24
  maskTest0_block_25)
  (interval_append maskTest0 416 432 448
  maskTest0_block_26
  maskTest0_block_27))
  (interval_append maskTest0 448 480 512
  (interval_append maskTest0 448 464 480
  maskTest0_block_28
  maskTest0_block_29)
  (interval_append maskTest0 480 496 512
  maskTest0_block_30
  maskTest0_block_31)))))
  (interval_append maskTest0 512 768 1024
  (interval_append maskTest0 512 640 768
  (interval_append maskTest0 512 576 640
  (interval_append maskTest0 512 544 576
  (interval_append maskTest0 512 528 544
  maskTest0_block_32
  maskTest0_block_33)
  (interval_append maskTest0 544 560 576
  maskTest0_block_34
  maskTest0_block_35))
  (interval_append maskTest0 576 608 640
  (interval_append maskTest0 576 592 608
  maskTest0_block_36
  maskTest0_block_37)
  (interval_append maskTest0 608 624 640
  maskTest0_block_38
  maskTest0_block_39)))
  (interval_append maskTest0 640 704 768
  (interval_append maskTest0 640 672 704
  (interval_append maskTest0 640 656 672
  maskTest0_block_40
  maskTest0_block_41)
  (interval_append maskTest0 672 688 704
  maskTest0_block_42
  maskTest0_block_43))
  (interval_append maskTest0 704 736 768
  (interval_append maskTest0 704 720 736
  maskTest0_block_44
  maskTest0_block_45)
  (interval_append maskTest0 736 752 768
  maskTest0_block_46
  maskTest0_block_47))))
  (interval_append maskTest0 768 896 1024
  (interval_append maskTest0 768 832 896
  (interval_append maskTest0 768 800 832
  (interval_append maskTest0 768 784 800
  maskTest0_block_48
  maskTest0_block_49)
  (interval_append maskTest0 800 816 832
  maskTest0_block_50
  maskTest0_block_51))
  (interval_append maskTest0 832 864 896
  (interval_append maskTest0 832 848 864
  maskTest0_block_52
  maskTest0_block_53)
  (interval_append maskTest0 864 880 896
  maskTest0_block_54
  maskTest0_block_55)))
  (interval_append maskTest0 896 960 1024
  (interval_append maskTest0 896 928 960
  (interval_append maskTest0 896 912 928
  maskTest0_block_56
  maskTest0_block_57)
  (interval_append maskTest0 928 944 960
  maskTest0_block_58
  maskTest0_block_59))
  (interval_append maskTest0 960 992 1024
  (interval_append maskTest0 960 976 992
  maskTest0_block_60
  maskTest0_block_61)
  (interval_append maskTest0 992 1008 1024
  maskTest0_block_62
  maskTest0_block_63))))))
cert_maskTest_2 1
cert_maskTest_block_2 1 0 0 16
cert_maskTest_block_2 1 1 16 32
cert_maskTest_block_2 1 2 32 48
cert_maskTest_block_2 1 3 48 64
cert_maskTest_block_2 1 4 64 80
cert_maskTest_block_2 1 5 80 96
cert_maskTest_block_2 1 6 96 112
cert_maskTest_block_2 1 7 112 128
cert_maskTest_block_2 1 8 128 144
cert_maskTest_block_2 1 9 144 160
cert_maskTest_block_2 1 10 160 176
cert_maskTest_block_2 1 11 176 192
cert_maskTest_block_2 1 12 192 208
cert_maskTest_block_2 1 13 208 224
cert_maskTest_block_2 1 14 224 240
cert_maskTest_block_2 1 15 240 256
cert_maskTest_block_2 1 16 256 272
cert_maskTest_block_2 1 17 272 288
cert_maskTest_block_2 1 18 288 304
cert_maskTest_block_2 1 19 304 320
cert_maskTest_block_2 1 20 320 336
cert_maskTest_block_2 1 21 336 352
cert_maskTest_block_2 1 22 352 368
cert_maskTest_block_2 1 23 368 384
cert_maskTest_block_2 1 24 384 400
cert_maskTest_block_2 1 25 400 416
cert_maskTest_block_2 1 26 416 432
cert_maskTest_block_2 1 27 432 448
cert_maskTest_block_2 1 28 448 464
cert_maskTest_block_2 1 29 464 480
cert_maskTest_block_2 1 30 480 496
cert_maskTest_block_2 1 31 496 512
cert_maskTest_block_2 1 32 512 528
cert_maskTest_block_2 1 33 528 544
cert_maskTest_block_2 1 34 544 560
cert_maskTest_block_2 1 35 560 576
cert_maskTest_block_2 1 36 576 592
cert_maskTest_block_2 1 37 592 608
cert_maskTest_block_2 1 38 608 624
cert_maskTest_block_2 1 39 624 640
cert_maskTest_block_2 1 40 640 656
cert_maskTest_block_2 1 41 656 672
cert_maskTest_block_2 1 42 672 688
cert_maskTest_block_2 1 43 688 704
cert_maskTest_block_2 1 44 704 720
cert_maskTest_block_2 1 45 720 736
cert_maskTest_block_2 1 46 736 752
cert_maskTest_block_2 1 47 752 768
cert_maskTest_block_2 1 48 768 784
cert_maskTest_block_2 1 49 784 800
cert_maskTest_block_2 1 50 800 816
cert_maskTest_block_2 1 51 816 832
cert_maskTest_block_2 1 52 832 848
cert_maskTest_block_2 1 53 848 864
cert_maskTest_block_2 1 54 864 880
cert_maskTest_block_2 1 55 880 896
cert_maskTest_block_2 1 56 896 912
cert_maskTest_block_2 1 57 912 928
cert_maskTest_block_2 1 58 928 944
cert_maskTest_block_2 1 59 944 960
cert_maskTest_block_2 1 60 960 976
cert_maskTest_block_2 1 61 976 992
cert_maskTest_block_2 1 62 992 1008
cert_maskTest_block_2 1 63 1008 1024
theorem maskTest1_complete : Interval maskTest1 0 1024 :=
  (interval_append maskTest1 0 512 1024
  (interval_append maskTest1 0 256 512
  (interval_append maskTest1 0 128 256
  (interval_append maskTest1 0 64 128
  (interval_append maskTest1 0 32 64
  (interval_append maskTest1 0 16 32
  maskTest1_block_0
  maskTest1_block_1)
  (interval_append maskTest1 32 48 64
  maskTest1_block_2
  maskTest1_block_3))
  (interval_append maskTest1 64 96 128
  (interval_append maskTest1 64 80 96
  maskTest1_block_4
  maskTest1_block_5)
  (interval_append maskTest1 96 112 128
  maskTest1_block_6
  maskTest1_block_7)))
  (interval_append maskTest1 128 192 256
  (interval_append maskTest1 128 160 192
  (interval_append maskTest1 128 144 160
  maskTest1_block_8
  maskTest1_block_9)
  (interval_append maskTest1 160 176 192
  maskTest1_block_10
  maskTest1_block_11))
  (interval_append maskTest1 192 224 256
  (interval_append maskTest1 192 208 224
  maskTest1_block_12
  maskTest1_block_13)
  (interval_append maskTest1 224 240 256
  maskTest1_block_14
  maskTest1_block_15))))
  (interval_append maskTest1 256 384 512
  (interval_append maskTest1 256 320 384
  (interval_append maskTest1 256 288 320
  (interval_append maskTest1 256 272 288
  maskTest1_block_16
  maskTest1_block_17)
  (interval_append maskTest1 288 304 320
  maskTest1_block_18
  maskTest1_block_19))
  (interval_append maskTest1 320 352 384
  (interval_append maskTest1 320 336 352
  maskTest1_block_20
  maskTest1_block_21)
  (interval_append maskTest1 352 368 384
  maskTest1_block_22
  maskTest1_block_23)))
  (interval_append maskTest1 384 448 512
  (interval_append maskTest1 384 416 448
  (interval_append maskTest1 384 400 416
  maskTest1_block_24
  maskTest1_block_25)
  (interval_append maskTest1 416 432 448
  maskTest1_block_26
  maskTest1_block_27))
  (interval_append maskTest1 448 480 512
  (interval_append maskTest1 448 464 480
  maskTest1_block_28
  maskTest1_block_29)
  (interval_append maskTest1 480 496 512
  maskTest1_block_30
  maskTest1_block_31)))))
  (interval_append maskTest1 512 768 1024
  (interval_append maskTest1 512 640 768
  (interval_append maskTest1 512 576 640
  (interval_append maskTest1 512 544 576
  (interval_append maskTest1 512 528 544
  maskTest1_block_32
  maskTest1_block_33)
  (interval_append maskTest1 544 560 576
  maskTest1_block_34
  maskTest1_block_35))
  (interval_append maskTest1 576 608 640
  (interval_append maskTest1 576 592 608
  maskTest1_block_36
  maskTest1_block_37)
  (interval_append maskTest1 608 624 640
  maskTest1_block_38
  maskTest1_block_39)))
  (interval_append maskTest1 640 704 768
  (interval_append maskTest1 640 672 704
  (interval_append maskTest1 640 656 672
  maskTest1_block_40
  maskTest1_block_41)
  (interval_append maskTest1 672 688 704
  maskTest1_block_42
  maskTest1_block_43))
  (interval_append maskTest1 704 736 768
  (interval_append maskTest1 704 720 736
  maskTest1_block_44
  maskTest1_block_45)
  (interval_append maskTest1 736 752 768
  maskTest1_block_46
  maskTest1_block_47))))
  (interval_append maskTest1 768 896 1024
  (interval_append maskTest1 768 832 896
  (interval_append maskTest1 768 800 832
  (interval_append maskTest1 768 784 800
  maskTest1_block_48
  maskTest1_block_49)
  (interval_append maskTest1 800 816 832
  maskTest1_block_50
  maskTest1_block_51))
  (interval_append maskTest1 832 864 896
  (interval_append maskTest1 832 848 864
  maskTest1_block_52
  maskTest1_block_53)
  (interval_append maskTest1 864 880 896
  maskTest1_block_54
  maskTest1_block_55)))
  (interval_append maskTest1 896 960 1024
  (interval_append maskTest1 896 928 960
  (interval_append maskTest1 896 912 928
  maskTest1_block_56
  maskTest1_block_57)
  (interval_append maskTest1 928 944 960
  maskTest1_block_58
  maskTest1_block_59))
  (interval_append maskTest1 960 992 1024
  (interval_append maskTest1 960 976 992
  maskTest1_block_60
  maskTest1_block_61)
  (interval_append maskTest1 992 1008 1024
  maskTest1_block_62
  maskTest1_block_63))))))
cert_mask_checked
cert_fastCellTest 655
cert_fastCellTest_eq
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed031.Outside.Verified
