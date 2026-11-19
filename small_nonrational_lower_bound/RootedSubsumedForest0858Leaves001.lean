module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0858Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
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
cert_leafTestAt_block_2 32 11 12
cert_leafTestAt_block_2 32 12 13
cert_leafTestAt_block_2 32 13 14
cert_leafTestAt_block_2 32 14 15
cert_leafTestAt_block_2 32 15 16
cert_leafTestAt_block_2 32 16 17
cert_leafTestAt_block_2 32 17 18
theorem leafTestAt32_complete : Interval leafTestAt32 0 18 :=
  (interval_append leafTestAt32 0 9 18
  (interval_append leafTestAt32 0 4 9
  (interval_append leafTestAt32 0 2 4
  (interval_append leafTestAt32 0 1 2
  leafTestAt32_block_0
  leafTestAt32_block_1)
  (interval_append leafTestAt32 2 3 4
  leafTestAt32_block_2
  leafTestAt32_block_3))
  (interval_append leafTestAt32 4 6 9
  (interval_append leafTestAt32 4 5 6
  leafTestAt32_block_4
  leafTestAt32_block_5)
  (interval_append leafTestAt32 6 7 9
  leafTestAt32_block_6
  (interval_append leafTestAt32 7 8 9
  leafTestAt32_block_7
  leafTestAt32_block_8))))
  (interval_append leafTestAt32 9 13 18
  (interval_append leafTestAt32 9 11 13
  (interval_append leafTestAt32 9 10 11
  leafTestAt32_block_9
  leafTestAt32_block_10)
  (interval_append leafTestAt32 11 12 13
  leafTestAt32_block_11
  leafTestAt32_block_12))
  (interval_append leafTestAt32 13 15 18
  (interval_append leafTestAt32 13 14 15
  leafTestAt32_block_13
  leafTestAt32_block_14)
  (interval_append leafTestAt32 15 16 18
  leafTestAt32_block_15
  (interval_append leafTestAt32 16 17 18
  leafTestAt32_block_16
  leafTestAt32_block_17)))))
cert_leafInterval 32 50
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
