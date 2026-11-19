module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0065Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0065
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 1280
cert_test_block_2 1280 0 0 32 32
cert_test_block_2 1280 1 32 64 32
cert_test_block_2 1280 2 64 96 32
cert_test_block_2 1280 3 96 121 25
theorem test1280_complete : Interval test1280 0 121 :=
  (interval_append test1280 0 64 121
  (interval_append test1280 0 32 64
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 64 96 121
  test1280_block_2
  test1280_block_3))
cert_nodeInterval_2 1280 1401
end Papers.RationalityTen.RootedForests.RootedRawForest0065
