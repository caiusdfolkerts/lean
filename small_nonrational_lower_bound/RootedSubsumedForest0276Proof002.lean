module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0276Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0276
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 1280
cert_test_block_3 1280 0 0 16 16
cert_test_block_3 1280 1 16 32 16
cert_test_block_3 1280 2 32 48 16
cert_test_block_3 1280 3 48 64 16
cert_test_block_3 1280 4 64 80 16
cert_test_block_3 1280 5 80 96 16
cert_test_block_3 1280 6 96 112 16
cert_test_block_3 1280 7 112 128 16
cert_test_block_3 1280 8 128 144 16
cert_test_block_3 1280 9 144 160 16
cert_test_block_3 1280 10 160 176 16
cert_test_block_3 1280 11 176 192 16
cert_test_block_3 1280 12 192 204 12
theorem test1280_complete : Interval test1280 0 204 :=
  (interval_append test1280 0 96 204
  (interval_append test1280 0 48 96
  (interval_append test1280 0 16 48
  test1280_block_0
  (interval_append test1280 16 32 48
  test1280_block_1
  test1280_block_2))
  (interval_append test1280 48 64 96
  test1280_block_3
  (interval_append test1280 64 80 96
  test1280_block_4
  test1280_block_5)))
  (interval_append test1280 96 144 204
  (interval_append test1280 96 112 144
  test1280_block_6
  (interval_append test1280 112 128 144
  test1280_block_7
  test1280_block_8))
  (interval_append test1280 144 176 204
  (interval_append test1280 144 160 176
  test1280_block_9
  test1280_block_10)
  (interval_append test1280 176 192 204
  test1280_block_11
  test1280_block_12))))
cert_nodeInterval_3 1280 1484
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0276
