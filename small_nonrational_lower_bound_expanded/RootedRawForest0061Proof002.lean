module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0061Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0061
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 1280
cert_test_block_2 1280 0 0 32 32
cert_test_block_2 1280 1 32 64 32
cert_test_block_2 1280 2 64 96 32
cert_test_block_2 1280 3 96 128 32
cert_test_block_2 1280 4 128 160 32
cert_test_block_2 1280 5 160 167 7
theorem test1280_complete : Interval test1280 0 167 :=
  (interval_append test1280 0 96 167
  (interval_append test1280 0 32 96
  test1280_block_0
  (interval_append test1280 32 64 96
  test1280_block_1
  test1280_block_2))
  (interval_append test1280 96 128 167
  test1280_block_3
  (interval_append test1280 128 160 167
  test1280_block_4
  test1280_block_5)))
cert_nodeInterval_2 1280 1447
end Papers.RationalityTen.RootedForests.RootedRawForest0061
