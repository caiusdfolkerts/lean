module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0299Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0299
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 14720
cert_test_block_3 14720 0 0 16 16
cert_test_block_3 14720 1 16 32 16
cert_test_block_3 14720 2 32 48 16
cert_test_block_3 14720 3 48 64 16
cert_test_block_3 14720 4 64 80 16
cert_test_block_3 14720 5 80 96 16
cert_test_block_3 14720 6 96 112 16
cert_test_block_3 14720 7 112 128 16
cert_test_block_3 14720 8 128 144 16
cert_test_block_3 14720 9 144 160 16
cert_test_block_3 14720 10 160 176 16
cert_test_block_3 14720 11 176 192 16
cert_test_block_3 14720 12 192 208 16
cert_test_block_3 14720 13 208 224 16
cert_test_block_3 14720 14 224 240 16
cert_test_block_3 14720 15 240 256 16
cert_test_block_3 14720 16 256 272 16
cert_test_block_3 14720 17 272 288 16
cert_test_block_3 14720 18 288 304 16
cert_test_block_3 14720 19 304 320 16
cert_test_block_3 14720 20 320 336 16
cert_test_block_3 14720 21 336 352 16
cert_test_block_3 14720 22 352 368 16
theorem test14720_complete : Interval test14720 0 368 :=
  (interval_append test14720 0 176 368
  (interval_append test14720 0 80 176
  (interval_append test14720 0 32 80
  (interval_append test14720 0 16 32
  test14720_block_0
  test14720_block_1)
  (interval_append test14720 32 48 80
  test14720_block_2
  (interval_append test14720 48 64 80
  test14720_block_3
  test14720_block_4)))
  (interval_append test14720 80 128 176
  (interval_append test14720 80 96 128
  test14720_block_5
  (interval_append test14720 96 112 128
  test14720_block_6
  test14720_block_7))
  (interval_append test14720 128 144 176
  test14720_block_8
  (interval_append test14720 144 160 176
  test14720_block_9
  test14720_block_10))))
  (interval_append test14720 176 272 368
  (interval_append test14720 176 224 272
  (interval_append test14720 176 192 224
  test14720_block_11
  (interval_append test14720 192 208 224
  test14720_block_12
  test14720_block_13))
  (interval_append test14720 224 240 272
  test14720_block_14
  (interval_append test14720 240 256 272
  test14720_block_15
  test14720_block_16)))
  (interval_append test14720 272 320 368
  (interval_append test14720 272 288 320
  test14720_block_17
  (interval_append test14720 288 304 320
  test14720_block_18
  test14720_block_19))
  (interval_append test14720 320 336 368
  test14720_block_20
  (interval_append test14720 336 352 368
  test14720_block_21
  test14720_block_22)))))
cert_nodeInterval_3 14720 15088
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0299
