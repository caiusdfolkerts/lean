module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0320Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 46720
cert_test_block_3 46720 0 0 16 16
cert_test_block_3 46720 1 16 32 16
cert_test_block_3 46720 2 32 48 16
cert_test_block_3 46720 3 48 64 16
cert_test_block_3 46720 4 64 80 16
cert_test_block_3 46720 5 80 96 16
cert_test_block_3 46720 6 96 112 16
cert_test_block_3 46720 7 112 128 16
cert_test_block_3 46720 8 128 144 16
cert_test_block_3 46720 9 144 160 16
cert_test_block_3 46720 10 160 176 16
cert_test_block_3 46720 11 176 192 16
cert_test_block_3 46720 12 192 208 16
cert_test_block_3 46720 13 208 224 16
cert_test_block_3 46720 14 224 240 16
cert_test_block_3 46720 15 240 256 16
cert_test_block_3 46720 16 256 272 16
cert_test_block_3 46720 17 272 288 16
cert_test_block_3 46720 18 288 304 16
cert_test_block_3 46720 19 304 320 16
cert_test_block_3 46720 20 320 336 16
cert_test_block_3 46720 21 336 352 16
cert_test_block_3 46720 22 352 368 16
cert_test_block_3 46720 23 368 384 16
cert_test_block_3 46720 24 384 400 16
cert_test_block_3 46720 25 400 402 2
theorem test46720_complete : Interval test46720 0 402 :=
  (interval_append test46720 0 208 402
  (interval_append test46720 0 96 208
  (interval_append test46720 0 48 96
  (interval_append test46720 0 16 48
  test46720_block_0
  (interval_append test46720 16 32 48
  test46720_block_1
  test46720_block_2))
  (interval_append test46720 48 64 96
  test46720_block_3
  (interval_append test46720 64 80 96
  test46720_block_4
  test46720_block_5)))
  (interval_append test46720 96 144 208
  (interval_append test46720 96 112 144
  test46720_block_6
  (interval_append test46720 112 128 144
  test46720_block_7
  test46720_block_8))
  (interval_append test46720 144 176 208
  (interval_append test46720 144 160 176
  test46720_block_9
  test46720_block_10)
  (interval_append test46720 176 192 208
  test46720_block_11
  test46720_block_12))))
  (interval_append test46720 208 304 402
  (interval_append test46720 208 256 304
  (interval_append test46720 208 224 256
  test46720_block_13
  (interval_append test46720 224 240 256
  test46720_block_14
  test46720_block_15))
  (interval_append test46720 256 272 304
  test46720_block_16
  (interval_append test46720 272 288 304
  test46720_block_17
  test46720_block_18)))
  (interval_append test46720 304 352 402
  (interval_append test46720 304 320 352
  test46720_block_19
  (interval_append test46720 320 336 352
  test46720_block_20
  test46720_block_21))
  (interval_append test46720 352 384 402
  (interval_append test46720 352 368 384
  test46720_block_22
  test46720_block_23)
  (interval_append test46720 384 400 402
  test46720_block_24
  test46720_block_25)))))
cert_nodeInterval_3 46720 47122
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
