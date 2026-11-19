module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed010Data

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed010
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
cert_cellTest_block_2 53 424 430 6
theorem cellTest_complete : Interval cellTest 0 430 :=
  (interval_append cellTest 0 216 430
  (interval_append cellTest 0 104 216
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
  (interval_append cellTest 104 160 216
  (interval_append cellTest 104 128 160
  (interval_append cellTest 104 112 128
  cellTest_block_13
  (interval_append cellTest 112 120 128
  cellTest_block_14
  cellTest_block_15))
  (interval_append cellTest 128 144 160
  (interval_append cellTest 128 136 144
  cellTest_block_16
  cellTest_block_17)
  (interval_append cellTest 144 152 160
  cellTest_block_18
  cellTest_block_19)))
  (interval_append cellTest 160 184 216
  (interval_append cellTest 160 168 184
  cellTest_block_20
  (interval_append cellTest 168 176 184
  cellTest_block_21
  cellTest_block_22))
  (interval_append cellTest 184 200 216
  (interval_append cellTest 184 192 200
  cellTest_block_23
  cellTest_block_24)
  (interval_append cellTest 200 208 216
  cellTest_block_25
  cellTest_block_26)))))
  (interval_append cellTest 216 320 430
  (interval_append cellTest 216 264 320
  (interval_append cellTest 216 240 264
  (interval_append cellTest 216 224 240
  cellTest_block_27
  (interval_append cellTest 224 232 240
  cellTest_block_28
  cellTest_block_29))
  (interval_append cellTest 240 248 264
  cellTest_block_30
  (interval_append cellTest 248 256 264
  cellTest_block_31
  cellTest_block_32)))
  (interval_append cellTest 264 288 320
  (interval_append cellTest 264 272 288
  cellTest_block_33
  (interval_append cellTest 272 280 288
  cellTest_block_34
  cellTest_block_35))
  (interval_append cellTest 288 304 320
  (interval_append cellTest 288 296 304
  cellTest_block_36
  cellTest_block_37)
  (interval_append cellTest 304 312 320
  cellTest_block_38
  cellTest_block_39))))
  (interval_append cellTest 320 376 430
  (interval_append cellTest 320 344 376
  (interval_append cellTest 320 328 344
  cellTest_block_40
  (interval_append cellTest 328 336 344
  cellTest_block_41
  cellTest_block_42))
  (interval_append cellTest 344 360 376
  (interval_append cellTest 344 352 360
  cellTest_block_43
  cellTest_block_44)
  (interval_append cellTest 360 368 376
  cellTest_block_45
  cellTest_block_46)))
  (interval_append cellTest 376 400 430
  (interval_append cellTest 376 384 400
  cellTest_block_47
  (interval_append cellTest 384 392 400
  cellTest_block_48
  cellTest_block_49))
  (interval_append cellTest 400 416 430
  (interval_append cellTest 400 408 416
  cellTest_block_50
  cellTest_block_51)
  (interval_append cellTest 416 424 430
  cellTest_block_52
  cellTest_block_53))))))
end Papers.RationalityTen.PackedReplay.PackedSevenMixed010
