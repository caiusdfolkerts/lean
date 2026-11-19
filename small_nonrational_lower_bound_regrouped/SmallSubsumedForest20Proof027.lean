module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest20Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 17280
cert_test_block_4 17280 0 0 16 16
cert_test_block_4 17280 1 16 32 16
cert_test_block_4 17280 2 32 48 16
cert_test_block_4 17280 3 48 64 16
cert_test_block_4 17280 4 64 80 16
cert_test_block_4 17280 5 80 96 16
cert_test_block_4 17280 6 96 112 16
cert_test_block_4 17280 7 112 128 16
cert_test_block_4 17280 8 128 144 16
cert_test_block_4 17280 9 144 160 16
cert_test_block_4 17280 10 160 176 16
cert_test_block_4 17280 11 176 192 16
cert_test_block_4 17280 12 192 208 16
cert_test_block_4 17280 13 208 224 16
cert_test_block_4 17280 14 224 240 16
cert_test_block_4 17280 15 240 256 16
cert_test_block_4 17280 16 256 272 16
cert_test_block_4 17280 17 272 288 16
cert_test_block_4 17280 18 288 304 16
cert_test_block_4 17280 19 304 320 16
cert_test_block_4 17280 20 320 336 16
cert_test_block_4 17280 21 336 352 16
cert_test_block_4 17280 22 352 368 16
cert_test_block_4 17280 23 368 384 16
cert_test_block_4 17280 24 384 400 16
cert_test_block_4 17280 25 400 416 16
cert_test_block_4 17280 26 416 432 16
cert_test_block_4 17280 27 432 448 16
cert_test_block_4 17280 28 448 464 16
cert_test_block_4 17280 29 464 480 16
cert_test_block_4 17280 30 480 496 16
cert_test_block_4 17280 31 496 503 7
theorem test17280_complete : Interval test17280 0 503 :=
  (interval_append test17280 0 256 503
  (interval_append test17280 0 128 256
  (interval_append test17280 0 64 128
  (interval_append test17280 0 32 64
  (interval_append test17280 0 16 32
  test17280_block_0
  test17280_block_1)
  (interval_append test17280 32 48 64
  test17280_block_2
  test17280_block_3))
  (interval_append test17280 64 96 128
  (interval_append test17280 64 80 96
  test17280_block_4
  test17280_block_5)
  (interval_append test17280 96 112 128
  test17280_block_6
  test17280_block_7)))
  (interval_append test17280 128 192 256
  (interval_append test17280 128 160 192
  (interval_append test17280 128 144 160
  test17280_block_8
  test17280_block_9)
  (interval_append test17280 160 176 192
  test17280_block_10
  test17280_block_11))
  (interval_append test17280 192 224 256
  (interval_append test17280 192 208 224
  test17280_block_12
  test17280_block_13)
  (interval_append test17280 224 240 256
  test17280_block_14
  test17280_block_15))))
  (interval_append test17280 256 384 503
  (interval_append test17280 256 320 384
  (interval_append test17280 256 288 320
  (interval_append test17280 256 272 288
  test17280_block_16
  test17280_block_17)
  (interval_append test17280 288 304 320
  test17280_block_18
  test17280_block_19))
  (interval_append test17280 320 352 384
  (interval_append test17280 320 336 352
  test17280_block_20
  test17280_block_21)
  (interval_append test17280 352 368 384
  test17280_block_22
  test17280_block_23)))
  (interval_append test17280 384 448 503
  (interval_append test17280 384 416 448
  (interval_append test17280 384 400 416
  test17280_block_24
  test17280_block_25)
  (interval_append test17280 416 432 448
  test17280_block_26
  test17280_block_27))
  (interval_append test17280 448 480 503
  (interval_append test17280 448 464 480
  test17280_block_28
  test17280_block_29)
  (interval_append test17280 480 496 503
  test17280_block_30
  test17280_block_31)))))
cert_nodeInterval_4 17280 17783
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
