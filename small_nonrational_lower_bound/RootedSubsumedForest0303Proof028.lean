module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0303Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 17920
cert_test_block_3 17920 0 0 16 16
cert_test_block_3 17920 1 16 32 16
cert_test_block_3 17920 2 32 48 16
cert_test_block_3 17920 3 48 64 16
cert_test_block_3 17920 4 64 80 16
cert_test_block_3 17920 5 80 96 16
cert_test_block_3 17920 6 96 112 16
cert_test_block_3 17920 7 112 128 16
cert_test_block_3 17920 8 128 144 16
cert_test_block_3 17920 9 144 160 16
cert_test_block_3 17920 10 160 176 16
cert_test_block_3 17920 11 176 192 16
cert_test_block_3 17920 12 192 208 16
cert_test_block_3 17920 13 208 224 16
cert_test_block_3 17920 14 224 240 16
cert_test_block_3 17920 15 240 256 16
cert_test_block_3 17920 16 256 272 16
cert_test_block_3 17920 17 272 288 16
cert_test_block_3 17920 18 288 304 16
cert_test_block_3 17920 19 304 320 16
cert_test_block_3 17920 20 320 336 16
cert_test_block_3 17920 21 336 352 16
cert_test_block_3 17920 22 352 368 16
cert_test_block_3 17920 23 368 384 16
cert_test_block_3 17920 24 384 400 16
cert_test_block_3 17920 25 400 416 16
cert_test_block_3 17920 26 416 432 16
cert_test_block_3 17920 27 432 437 5
theorem test17920_complete : Interval test17920 0 437 :=
  (interval_append test17920 0 224 437
  (interval_append test17920 0 112 224
  (interval_append test17920 0 48 112
  (interval_append test17920 0 16 48
  test17920_block_0
  (interval_append test17920 16 32 48
  test17920_block_1
  test17920_block_2))
  (interval_append test17920 48 80 112
  (interval_append test17920 48 64 80
  test17920_block_3
  test17920_block_4)
  (interval_append test17920 80 96 112
  test17920_block_5
  test17920_block_6)))
  (interval_append test17920 112 160 224
  (interval_append test17920 112 128 160
  test17920_block_7
  (interval_append test17920 128 144 160
  test17920_block_8
  test17920_block_9))
  (interval_append test17920 160 192 224
  (interval_append test17920 160 176 192
  test17920_block_10
  test17920_block_11)
  (interval_append test17920 192 208 224
  test17920_block_12
  test17920_block_13))))
  (interval_append test17920 224 336 437
  (interval_append test17920 224 272 336
  (interval_append test17920 224 240 272
  test17920_block_14
  (interval_append test17920 240 256 272
  test17920_block_15
  test17920_block_16))
  (interval_append test17920 272 304 336
  (interval_append test17920 272 288 304
  test17920_block_17
  test17920_block_18)
  (interval_append test17920 304 320 336
  test17920_block_19
  test17920_block_20)))
  (interval_append test17920 336 384 437
  (interval_append test17920 336 352 384
  test17920_block_21
  (interval_append test17920 352 368 384
  test17920_block_22
  test17920_block_23))
  (interval_append test17920 384 416 437
  (interval_append test17920 384 400 416
  test17920_block_24
  test17920_block_25)
  (interval_append test17920 416 432 437
  test17920_block_26
  test17920_block_27)))))
cert_nodeInterval_3 17920 18357
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
