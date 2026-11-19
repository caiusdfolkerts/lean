module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0743Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 43520
cert_test_block_3 43520 0 0 16 16
cert_test_block_3 43520 1 16 32 16
cert_test_block_3 43520 2 32 48 16
cert_test_block_3 43520 3 48 64 16
cert_test_block_3 43520 4 64 80 16
cert_test_block_3 43520 5 80 96 16
cert_test_block_3 43520 6 96 112 16
cert_test_block_3 43520 7 112 128 16
cert_test_block_3 43520 8 128 144 16
cert_test_block_3 43520 9 144 160 16
cert_test_block_3 43520 10 160 176 16
cert_test_block_3 43520 11 176 192 16
cert_test_block_3 43520 12 192 208 16
cert_test_block_3 43520 13 208 224 16
cert_test_block_3 43520 14 224 240 16
cert_test_block_3 43520 15 240 256 16
cert_test_block_3 43520 16 256 272 16
cert_test_block_3 43520 17 272 288 16
cert_test_block_3 43520 18 288 304 16
cert_test_block_3 43520 19 304 320 16
cert_test_block_3 43520 20 320 336 16
cert_test_block_3 43520 21 336 352 16
cert_test_block_3 43520 22 352 368 16
cert_test_block_3 43520 23 368 384 16
cert_test_block_3 43520 24 384 400 16
cert_test_block_3 43520 25 400 416 16
cert_test_block_3 43520 26 416 429 13
theorem test43520_complete : Interval test43520 0 429 :=
  (interval_append test43520 0 208 429
  (interval_append test43520 0 96 208
  (interval_append test43520 0 48 96
  (interval_append test43520 0 16 48
  test43520_block_0
  (interval_append test43520 16 32 48
  test43520_block_1
  test43520_block_2))
  (interval_append test43520 48 64 96
  test43520_block_3
  (interval_append test43520 64 80 96
  test43520_block_4
  test43520_block_5)))
  (interval_append test43520 96 144 208
  (interval_append test43520 96 112 144
  test43520_block_6
  (interval_append test43520 112 128 144
  test43520_block_7
  test43520_block_8))
  (interval_append test43520 144 176 208
  (interval_append test43520 144 160 176
  test43520_block_9
  test43520_block_10)
  (interval_append test43520 176 192 208
  test43520_block_11
  test43520_block_12))))
  (interval_append test43520 208 320 429
  (interval_append test43520 208 256 320
  (interval_append test43520 208 224 256
  test43520_block_13
  (interval_append test43520 224 240 256
  test43520_block_14
  test43520_block_15))
  (interval_append test43520 256 288 320
  (interval_append test43520 256 272 288
  test43520_block_16
  test43520_block_17)
  (interval_append test43520 288 304 320
  test43520_block_18
  test43520_block_19)))
  (interval_append test43520 320 368 429
  (interval_append test43520 320 336 368
  test43520_block_20
  (interval_append test43520 336 352 368
  test43520_block_21
  test43520_block_22))
  (interval_append test43520 368 400 429
  (interval_append test43520 368 384 400
  test43520_block_23
  test43520_block_24)
  (interval_append test43520 400 416 429
  test43520_block_25
  test43520_block_26)))))
cert_nodeInterval_3 43520 43949
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
