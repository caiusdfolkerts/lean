module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest11Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt_2 32
cert_leafTestAt_block_3 32 0 1
cert_leafTestAt_block_3 32 1 2
cert_leafTestAt_block_3 32 2 3
cert_leafTestAt_block_3 32 3 4
cert_leafTestAt_block_3 32 4 5
cert_leafTestAt_block_3 32 5 6
cert_leafTestAt_block_3 32 6 7
theorem leafTestAt32_complete : Interval leafTestAt32 0 7 :=
  (interval_append leafTestAt32 0 3 7
  (interval_append leafTestAt32 0 1 3
  leafTestAt32_block_0
  (interval_append leafTestAt32 1 2 3
  leafTestAt32_block_1
  leafTestAt32_block_2))
  (interval_append leafTestAt32 3 5 7
  (interval_append leafTestAt32 3 4 5
  leafTestAt32_block_3
  leafTestAt32_block_4)
  (interval_append leafTestAt32 5 6 7
  leafTestAt32_block_5
  leafTestAt32_block_6)))
cert_leafInterval_2 32 39
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
