module
prelude
public import PackedSevenMixed015Data

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed015
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

theorem cellTest_block_65 : Interval cellTest 520 521 :=
  interval_of_check cellTest 520 1 (by decide +kernel)

theorem cellTest_complete : Interval cellTest 0 521 :=
  (interval_append cellTest 0 264 521
  (interval_append cellTest 0 128 264
  (interval_append cellTest 0 64 128
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
  (interval_append cellTest 64 96 128
  (interval_append cellTest 64 80 96
  (interval_append cellTest 64 72 80
  cellTest_block_8
  cellTest_block_9)
  (interval_append cellTest 80 88 96
  cellTest_block_10
  cellTest_block_11))
  (interval_append cellTest 96 112 128
  (interval_append cellTest 96 104 112
  cellTest_block_12
  cellTest_block_13)
  (interval_append cellTest 112 120 128
  cellTest_block_14
  cellTest_block_15))))
  (interval_append cellTest 128 192 264
  (interval_append cellTest 128 160 192
  (interval_append cellTest 128 144 160
  (interval_append cellTest 128 136 144
  cellTest_block_16
  cellTest_block_17)
  (interval_append cellTest 144 152 160
  cellTest_block_18
  cellTest_block_19))
  (interval_append cellTest 160 176 192
  (interval_append cellTest 160 168 176
  cellTest_block_20
  cellTest_block_21)
  (interval_append cellTest 176 184 192
  cellTest_block_22
  cellTest_block_23)))
  (interval_append cellTest 192 224 264
  (interval_append cellTest 192 208 224
  (interval_append cellTest 192 200 208
  cellTest_block_24
  cellTest_block_25)
  (interval_append cellTest 208 216 224
  cellTest_block_26
  cellTest_block_27))
  (interval_append cellTest 224 240 264
  (interval_append cellTest 224 232 240
  cellTest_block_28
  cellTest_block_29)
  (interval_append cellTest 240 248 264
  cellTest_block_30
  (interval_append cellTest 248 256 264
  cellTest_block_31
  cellTest_block_32))))))
  (interval_append cellTest 264 392 521
  (interval_append cellTest 264 328 392
  (interval_append cellTest 264 296 328
  (interval_append cellTest 264 280 296
  (interval_append cellTest 264 272 280
  cellTest_block_33
  cellTest_block_34)
  (interval_append cellTest 280 288 296
  cellTest_block_35
  cellTest_block_36))
  (interval_append cellTest 296 312 328
  (interval_append cellTest 296 304 312
  cellTest_block_37
  cellTest_block_38)
  (interval_append cellTest 312 320 328
  cellTest_block_39
  cellTest_block_40)))
  (interval_append cellTest 328 360 392
  (interval_append cellTest 328 344 360
  (interval_append cellTest 328 336 344
  cellTest_block_41
  cellTest_block_42)
  (interval_append cellTest 344 352 360
  cellTest_block_43
  cellTest_block_44))
  (interval_append cellTest 360 376 392
  (interval_append cellTest 360 368 376
  cellTest_block_45
  cellTest_block_46)
  (interval_append cellTest 376 384 392
  cellTest_block_47
  cellTest_block_48))))
  (interval_append cellTest 392 456 521
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
  cellTest_block_56)))
  (interval_append cellTest 456 488 521
  (interval_append cellTest 456 472 488
  (interval_append cellTest 456 464 472
  cellTest_block_57
  cellTest_block_58)
  (interval_append cellTest 472 480 488
  cellTest_block_59
  cellTest_block_60))
  (interval_append cellTest 488 504 521
  (interval_append cellTest 488 496 504
  cellTest_block_61
  cellTest_block_62)
  (interval_append cellTest 504 512 521
  cellTest_block_63
  (interval_append cellTest 512 520 521
  cellTest_block_64
  cellTest_block_65)))))))
end Papers.RationalityTen.PackedReplay.PackedSevenMixed015
