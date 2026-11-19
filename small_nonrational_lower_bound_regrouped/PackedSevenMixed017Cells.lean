module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed017Data

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed017
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
cert_cellTest_block_2 80 640 646 6
theorem cellTest_complete : Interval cellTest 0 646 :=
  (interval_append cellTest 0 320 646
  (interval_append cellTest 0 160 320
  (interval_append cellTest 0 80 160
  (interval_append cellTest 0 40 80
  (interval_append cellTest 0 16 40
  (interval_append cellTest 0 8 16
  cellTest_block_0
  cellTest_block_1)
  (interval_append cellTest 16 24 40
  cellTest_block_2
  (interval_append cellTest 24 32 40
  cellTest_block_3
  cellTest_block_4)))
  (interval_append cellTest 40 56 80
  (interval_append cellTest 40 48 56
  cellTest_block_5
  cellTest_block_6)
  (interval_append cellTest 56 64 80
  cellTest_block_7
  (interval_append cellTest 64 72 80
  cellTest_block_8
  cellTest_block_9))))
  (interval_append cellTest 80 120 160
  (interval_append cellTest 80 96 120
  (interval_append cellTest 80 88 96
  cellTest_block_10
  cellTest_block_11)
  (interval_append cellTest 96 104 120
  cellTest_block_12
  (interval_append cellTest 104 112 120
  cellTest_block_13
  cellTest_block_14)))
  (interval_append cellTest 120 136 160
  (interval_append cellTest 120 128 136
  cellTest_block_15
  cellTest_block_16)
  (interval_append cellTest 136 144 160
  cellTest_block_17
  (interval_append cellTest 144 152 160
  cellTest_block_18
  cellTest_block_19)))))
  (interval_append cellTest 160 240 320
  (interval_append cellTest 160 200 240
  (interval_append cellTest 160 176 200
  (interval_append cellTest 160 168 176
  cellTest_block_20
  cellTest_block_21)
  (interval_append cellTest 176 184 200
  cellTest_block_22
  (interval_append cellTest 184 192 200
  cellTest_block_23
  cellTest_block_24)))
  (interval_append cellTest 200 216 240
  (interval_append cellTest 200 208 216
  cellTest_block_25
  cellTest_block_26)
  (interval_append cellTest 216 224 240
  cellTest_block_27
  (interval_append cellTest 224 232 240
  cellTest_block_28
  cellTest_block_29))))
  (interval_append cellTest 240 280 320
  (interval_append cellTest 240 256 280
  (interval_append cellTest 240 248 256
  cellTest_block_30
  cellTest_block_31)
  (interval_append cellTest 256 264 280
  cellTest_block_32
  (interval_append cellTest 264 272 280
  cellTest_block_33
  cellTest_block_34)))
  (interval_append cellTest 280 296 320
  (interval_append cellTest 280 288 296
  cellTest_block_35
  cellTest_block_36)
  (interval_append cellTest 296 304 320
  cellTest_block_37
  (interval_append cellTest 304 312 320
  cellTest_block_38
  cellTest_block_39))))))
  (interval_append cellTest 320 480 646
  (interval_append cellTest 320 400 480
  (interval_append cellTest 320 360 400
  (interval_append cellTest 320 336 360
  (interval_append cellTest 320 328 336
  cellTest_block_40
  cellTest_block_41)
  (interval_append cellTest 336 344 360
  cellTest_block_42
  (interval_append cellTest 344 352 360
  cellTest_block_43
  cellTest_block_44)))
  (interval_append cellTest 360 376 400
  (interval_append cellTest 360 368 376
  cellTest_block_45
  cellTest_block_46)
  (interval_append cellTest 376 384 400
  cellTest_block_47
  (interval_append cellTest 384 392 400
  cellTest_block_48
  cellTest_block_49))))
  (interval_append cellTest 400 440 480
  (interval_append cellTest 400 416 440
  (interval_append cellTest 400 408 416
  cellTest_block_50
  cellTest_block_51)
  (interval_append cellTest 416 424 440
  cellTest_block_52
  (interval_append cellTest 424 432 440
  cellTest_block_53
  cellTest_block_54)))
  (interval_append cellTest 440 456 480
  (interval_append cellTest 440 448 456
  cellTest_block_55
  cellTest_block_56)
  (interval_append cellTest 456 464 480
  cellTest_block_57
  (interval_append cellTest 464 472 480
  cellTest_block_58
  cellTest_block_59)))))
  (interval_append cellTest 480 560 646
  (interval_append cellTest 480 520 560
  (interval_append cellTest 480 496 520
  (interval_append cellTest 480 488 496
  cellTest_block_60
  cellTest_block_61)
  (interval_append cellTest 496 504 520
  cellTest_block_62
  (interval_append cellTest 504 512 520
  cellTest_block_63
  cellTest_block_64)))
  (interval_append cellTest 520 536 560
  (interval_append cellTest 520 528 536
  cellTest_block_65
  cellTest_block_66)
  (interval_append cellTest 536 544 560
  cellTest_block_67
  (interval_append cellTest 544 552 560
  cellTest_block_68
  cellTest_block_69))))
  (interval_append cellTest 560 600 646
  (interval_append cellTest 560 576 600
  (interval_append cellTest 560 568 576
  cellTest_block_70
  cellTest_block_71)
  (interval_append cellTest 576 584 600
  cellTest_block_72
  (interval_append cellTest 584 592 600
  cellTest_block_73
  cellTest_block_74)))
  (interval_append cellTest 600 624 646
  (interval_append cellTest 600 608 624
  cellTest_block_75
  (interval_append cellTest 608 616 624
  cellTest_block_76
  cellTest_block_77))
  (interval_append cellTest 624 632 646
  cellTest_block_78
  (interval_append cellTest 632 640 646
  cellTest_block_79
  cellTest_block_80)))))))
end Papers.RationalityTen.PackedReplay.PackedSevenMixed017
