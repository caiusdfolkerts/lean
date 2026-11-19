module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0868Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 160
cert_leafTestAt_block_2 160 0 1
cert_leafTestAt_block_2 160 1 2
cert_leafTestAt_block_2 160 2 3
cert_leafTestAt_block_2 160 3 4
cert_leafTestAt_block_2 160 4 5
cert_leafTestAt_block_2 160 5 6
cert_leafTestAt_block_2 160 6 7
cert_leafTestAt_block_2 160 7 8
cert_leafTestAt_block_2 160 8 9
cert_leafTestAt_block_2 160 9 10
cert_leafTestAt_block_2 160 10 11
cert_leafTestAt_block_2 160 11 12
cert_leafTestAt_block_2 160 12 13
cert_leafTestAt_block_2 160 13 14
cert_leafTestAt_block_2 160 14 15
cert_leafTestAt_block_2 160 15 16
cert_leafTestAt_block_2 160 16 17
cert_leafTestAt_block_2 160 17 18
cert_leafTestAt_block_2 160 18 19
cert_leafTestAt_block_2 160 19 20
theorem leafTestAt160_complete : Interval leafTestAt160 0 20 :=
  (interval_append leafTestAt160 0 10 20
  (interval_append leafTestAt160 0 5 10
  (interval_append leafTestAt160 0 2 5
  (interval_append leafTestAt160 0 1 2
  leafTestAt160_block_0
  leafTestAt160_block_1)
  (interval_append leafTestAt160 2 3 5
  leafTestAt160_block_2
  (interval_append leafTestAt160 3 4 5
  leafTestAt160_block_3
  leafTestAt160_block_4)))
  (interval_append leafTestAt160 5 7 10
  (interval_append leafTestAt160 5 6 7
  leafTestAt160_block_5
  leafTestAt160_block_6)
  (interval_append leafTestAt160 7 8 10
  leafTestAt160_block_7
  (interval_append leafTestAt160 8 9 10
  leafTestAt160_block_8
  leafTestAt160_block_9))))
  (interval_append leafTestAt160 10 15 20
  (interval_append leafTestAt160 10 12 15
  (interval_append leafTestAt160 10 11 12
  leafTestAt160_block_10
  leafTestAt160_block_11)
  (interval_append leafTestAt160 12 13 15
  leafTestAt160_block_12
  (interval_append leafTestAt160 13 14 15
  leafTestAt160_block_13
  leafTestAt160_block_14)))
  (interval_append leafTestAt160 15 17 20
  (interval_append leafTestAt160 15 16 17
  leafTestAt160_block_15
  leafTestAt160_block_16)
  (interval_append leafTestAt160 17 18 20
  leafTestAt160_block_17
  (interval_append leafTestAt160 18 19 20
  leafTestAt160_block_18
  leafTestAt160_block_19)))))
cert_leafInterval 160 180
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
