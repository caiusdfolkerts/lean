module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest08Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 61440
cert_test_block_4 61440 0 0 16 16
cert_test_block_4 61440 1 16 32 16
cert_test_block_4 61440 2 32 48 16
cert_test_block_4 61440 3 48 64 16
cert_test_block_4 61440 4 64 80 16
cert_test_block_4 61440 5 80 96 16
cert_test_block_4 61440 6 96 112 16
cert_test_block_4 61440 7 112 128 16
cert_test_block_4 61440 8 128 144 16
cert_test_block_4 61440 9 144 160 16
cert_test_block_4 61440 10 160 176 16
cert_test_block_4 61440 11 176 192 16
cert_test_block_4 61440 12 192 208 16
cert_test_block_4 61440 13 208 224 16
cert_test_block_4 61440 14 224 240 16
cert_test_block_4 61440 15 240 256 16
cert_test_block_4 61440 16 256 272 16
cert_test_block_4 61440 17 272 288 16
cert_test_block_4 61440 18 288 304 16
cert_test_block_4 61440 19 304 313 9
theorem test61440_complete : Interval test61440 0 313 :=
  (interval_append test61440 0 160 313
  (interval_append test61440 0 80 160
  (interval_append test61440 0 32 80
  (interval_append test61440 0 16 32
  test61440_block_0
  test61440_block_1)
  (interval_append test61440 32 48 80
  test61440_block_2
  (interval_append test61440 48 64 80
  test61440_block_3
  test61440_block_4)))
  (interval_append test61440 80 112 160
  (interval_append test61440 80 96 112
  test61440_block_5
  test61440_block_6)
  (interval_append test61440 112 128 160
  test61440_block_7
  (interval_append test61440 128 144 160
  test61440_block_8
  test61440_block_9))))
  (interval_append test61440 160 240 313
  (interval_append test61440 160 192 240
  (interval_append test61440 160 176 192
  test61440_block_10
  test61440_block_11)
  (interval_append test61440 192 208 240
  test61440_block_12
  (interval_append test61440 208 224 240
  test61440_block_13
  test61440_block_14)))
  (interval_append test61440 240 272 313
  (interval_append test61440 240 256 272
  test61440_block_15
  test61440_block_16)
  (interval_append test61440 272 288 313
  test61440_block_17
  (interval_append test61440 288 304 313
  test61440_block_18
  test61440_block_19)))))
cert_nodeInterval_4 61440 61753
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
