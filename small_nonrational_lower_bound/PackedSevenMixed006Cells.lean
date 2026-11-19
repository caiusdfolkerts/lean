module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed006Data

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed006
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
cert_cellTest_block_2 69 552 556 4
theorem cellTest_complete : Interval cellTest 0 556 :=
  (interval_append cellTest 0 280 556
  (interval_append cellTest 0 136 280
  (interval_append cellTest 0 64 136
  (interval_append cellTest 0 32 64
  (interval_append cellTest 0 16 32
  (interval_append cellTest 0 8 16
  cellTest_block_0
  cellTest_block_1)
  (interval_append cellTest 16 24 32
  cellTest_block_2
  cellTest_block_3))
  (interval_append cellTest 32 48 64
  (interval_append cellTest 32 40 48
  cellTest_block_4
  cellTest_block_5)
  (interval_append cellTest 48 56 64
  cellTest_block_6
  cellTest_block_7)))
  (interval_append cellTest 64 96 136
  (interval_append cellTest 64 80 96
  (interval_append cellTest 64 72 80
  cellTest_block_8
  cellTest_block_9)
  (interval_append cellTest 80 88 96
  cellTest_block_10
  cellTest_block_11))
  (interval_append cellTest 96 112 136
  (interval_append cellTest 96 104 112
  cellTest_block_12
  cellTest_block_13)
  (interval_append cellTest 112 120 136
  cellTest_block_14
  (interval_append cellTest 120 128 136
  cellTest_block_15
  cellTest_block_16)))))
  (interval_append cellTest 136 208 280
  (interval_append cellTest 136 168 208
  (interval_append cellTest 136 152 168
  (interval_append cellTest 136 144 152
  cellTest_block_17
  cellTest_block_18)
  (interval_append cellTest 152 160 168
  cellTest_block_19
  cellTest_block_20))
  (interval_append cellTest 168 184 208
  (interval_append cellTest 168 176 184
  cellTest_block_21
  cellTest_block_22)
  (interval_append cellTest 184 192 208
  cellTest_block_23
  (interval_append cellTest 192 200 208
  cellTest_block_24
  cellTest_block_25))))
  (interval_append cellTest 208 240 280
  (interval_append cellTest 208 224 240
  (interval_append cellTest 208 216 224
  cellTest_block_26
  cellTest_block_27)
  (interval_append cellTest 224 232 240
  cellTest_block_28
  cellTest_block_29))
  (interval_append cellTest 240 256 280
  (interval_append cellTest 240 248 256
  cellTest_block_30
  cellTest_block_31)
  (interval_append cellTest 256 264 280
  cellTest_block_32
  (interval_append cellTest 264 272 280
  cellTest_block_33
  cellTest_block_34))))))
  (interval_append cellTest 280 416 556
  (interval_append cellTest 280 344 416
  (interval_append cellTest 280 312 344
  (interval_append cellTest 280 296 312
  (interval_append cellTest 280 288 296
  cellTest_block_35
  cellTest_block_36)
  (interval_append cellTest 296 304 312
  cellTest_block_37
  cellTest_block_38))
  (interval_append cellTest 312 328 344
  (interval_append cellTest 312 320 328
  cellTest_block_39
  cellTest_block_40)
  (interval_append cellTest 328 336 344
  cellTest_block_41
  cellTest_block_42)))
  (interval_append cellTest 344 376 416
  (interval_append cellTest 344 360 376
  (interval_append cellTest 344 352 360
  cellTest_block_43
  cellTest_block_44)
  (interval_append cellTest 360 368 376
  cellTest_block_45
  cellTest_block_46))
  (interval_append cellTest 376 392 416
  (interval_append cellTest 376 384 392
  cellTest_block_47
  cellTest_block_48)
  (interval_append cellTest 392 400 416
  cellTest_block_49
  (interval_append cellTest 400 408 416
  cellTest_block_50
  cellTest_block_51)))))
  (interval_append cellTest 416 488 556
  (interval_append cellTest 416 448 488
  (interval_append cellTest 416 432 448
  (interval_append cellTest 416 424 432
  cellTest_block_52
  cellTest_block_53)
  (interval_append cellTest 432 440 448
  cellTest_block_54
  cellTest_block_55))
  (interval_append cellTest 448 464 488
  (interval_append cellTest 448 456 464
  cellTest_block_56
  cellTest_block_57)
  (interval_append cellTest 464 472 488
  cellTest_block_58
  (interval_append cellTest 472 480 488
  cellTest_block_59
  cellTest_block_60))))
  (interval_append cellTest 488 520 556
  (interval_append cellTest 488 504 520
  (interval_append cellTest 488 496 504
  cellTest_block_61
  cellTest_block_62)
  (interval_append cellTest 504 512 520
  cellTest_block_63
  cellTest_block_64))
  (interval_append cellTest 520 536 556
  (interval_append cellTest 520 528 536
  cellTest_block_65
  cellTest_block_66)
  (interval_append cellTest 536 544 556
  cellTest_block_67
  (interval_append cellTest 544 552 556
  cellTest_block_68
  cellTest_block_69)))))))
end Papers.RationalityTen.PackedReplay.PackedSevenMixed006
