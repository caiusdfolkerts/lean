module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest10Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 10240
cert_test_block_4 10240 0 0 16 16
cert_test_block_4 10240 1 16 32 16
cert_test_block_4 10240 2 32 48 16
cert_test_block_4 10240 3 48 64 16
cert_test_block_4 10240 4 64 80 16
cert_test_block_4 10240 5 80 96 16
cert_test_block_4 10240 6 96 112 16
cert_test_block_4 10240 7 112 128 16
cert_test_block_4 10240 8 128 144 16
cert_test_block_4 10240 9 144 160 16
cert_test_block_4 10240 10 160 176 16
cert_test_block_4 10240 11 176 192 16
cert_test_block_4 10240 12 192 208 16
cert_test_block_4 10240 13 208 224 16
cert_test_block_4 10240 14 224 240 16
cert_test_block_4 10240 15 240 256 16
cert_test_block_4 10240 16 256 272 16
cert_test_block_4 10240 17 272 288 16
cert_test_block_4 10240 18 288 289 1
theorem test10240_complete : Interval test10240 0 289 :=
  (interval_append test10240 0 144 289
  (interval_append test10240 0 64 144
  (interval_append test10240 0 32 64
  (interval_append test10240 0 16 32
  test10240_block_0
  test10240_block_1)
  (interval_append test10240 32 48 64
  test10240_block_2
  test10240_block_3))
  (interval_append test10240 64 96 144
  (interval_append test10240 64 80 96
  test10240_block_4
  test10240_block_5)
  (interval_append test10240 96 112 144
  test10240_block_6
  (interval_append test10240 112 128 144
  test10240_block_7
  test10240_block_8))))
  (interval_append test10240 144 224 289
  (interval_append test10240 144 176 224
  (interval_append test10240 144 160 176
  test10240_block_9
  test10240_block_10)
  (interval_append test10240 176 192 224
  test10240_block_11
  (interval_append test10240 192 208 224
  test10240_block_12
  test10240_block_13)))
  (interval_append test10240 224 256 289
  (interval_append test10240 224 240 256
  test10240_block_14
  test10240_block_15)
  (interval_append test10240 256 272 289
  test10240_block_16
  (interval_append test10240 272 288 289
  test10240_block_17
  test10240_block_18)))))
cert_nodeInterval_4 10240 10529
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
