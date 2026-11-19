module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0298Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 32
cert_leafTestAt_block_2 32 0 1
cert_leafTestAt_block_2 32 1 2
cert_leafTestAt_block_2 32 2 3
cert_leafTestAt_block_2 32 3 4
cert_leafTestAt_block_2 32 4 5
cert_leafTestAt_block_2 32 5 6
cert_leafTestAt_block_2 32 6 7
cert_leafTestAt_block_2 32 7 8
cert_leafTestAt_block_2 32 8 9
cert_leafTestAt_block_2 32 9 10
cert_leafTestAt_block_2 32 10 11
theorem leafTestAt32_complete : Interval leafTestAt32 0 11 :=
  (interval_append leafTestAt32 0 5 11
  (interval_append leafTestAt32 0 2 5
  (interval_append leafTestAt32 0 1 2
  leafTestAt32_block_0
  leafTestAt32_block_1)
  (interval_append leafTestAt32 2 3 5
  leafTestAt32_block_2
  (interval_append leafTestAt32 3 4 5
  leafTestAt32_block_3
  leafTestAt32_block_4)))
  (interval_append leafTestAt32 5 8 11
  (interval_append leafTestAt32 5 6 8
  leafTestAt32_block_5
  (interval_append leafTestAt32 6 7 8
  leafTestAt32_block_6
  leafTestAt32_block_7))
  (interval_append leafTestAt32 8 9 11
  leafTestAt32_block_8
  (interval_append leafTestAt32 9 10 11
  leafTestAt32_block_9
  leafTestAt32_block_10))))
cert_leafInterval 32 43
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
