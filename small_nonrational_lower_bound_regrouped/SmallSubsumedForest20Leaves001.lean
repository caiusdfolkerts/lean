module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest20Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
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
cert_leafTestAt_block_3 32 7 8
cert_leafTestAt_block_3 32 8 9
cert_leafTestAt_block_3 32 9 10
cert_leafTestAt_block_3 32 10 11
cert_leafTestAt_block_3 32 11 12
cert_leafTestAt_block_3 32 12 13
cert_leafTestAt_block_3 32 13 14
cert_leafTestAt_block_3 32 14 15
cert_leafTestAt_block_3 32 15 16
cert_leafTestAt_block_3 32 16 17
cert_leafTestAt_block_3 32 17 18
cert_leafTestAt_block_3 32 18 19
cert_leafTestAt_block_3 32 19 20
cert_leafTestAt_block_3 32 20 21
cert_leafTestAt_block_3 32 21 22
cert_leafTestAt_block_3 32 22 23
cert_leafTestAt_block_3 32 23 24
cert_leafTestAt_block_3 32 24 25
cert_leafTestAt_block_3 32 25 26
cert_leafTestAt_block_3 32 26 27
cert_leafTestAt_block_3 32 27 28
cert_leafTestAt_block_3 32 28 29
theorem leafTestAt32_complete : Interval leafTestAt32 0 29 :=
  (interval_append leafTestAt32 0 14 29
  (interval_append leafTestAt32 0 7 14
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
  (interval_append leafTestAt32 7 10 14
  (interval_append leafTestAt32 7 8 10
  leafTestAt32_block_7
  (interval_append leafTestAt32 8 9 10
  leafTestAt32_block_8
  leafTestAt32_block_9))
  (interval_append leafTestAt32 10 12 14
  (interval_append leafTestAt32 10 11 12
  leafTestAt32_block_10
  leafTestAt32_block_11)
  (interval_append leafTestAt32 12 13 14
  leafTestAt32_block_12
  leafTestAt32_block_13))))
  (interval_append leafTestAt32 14 21 29
  (interval_append leafTestAt32 14 17 21
  (interval_append leafTestAt32 14 15 17
  leafTestAt32_block_14
  (interval_append leafTestAt32 15 16 17
  leafTestAt32_block_15
  leafTestAt32_block_16))
  (interval_append leafTestAt32 17 19 21
  (interval_append leafTestAt32 17 18 19
  leafTestAt32_block_17
  leafTestAt32_block_18)
  (interval_append leafTestAt32 19 20 21
  leafTestAt32_block_19
  leafTestAt32_block_20)))
  (interval_append leafTestAt32 21 25 29
  (interval_append leafTestAt32 21 23 25
  (interval_append leafTestAt32 21 22 23
  leafTestAt32_block_21
  leafTestAt32_block_22)
  (interval_append leafTestAt32 23 24 25
  leafTestAt32_block_23
  leafTestAt32_block_24))
  (interval_append leafTestAt32 25 27 29
  (interval_append leafTestAt32 25 26 27
  leafTestAt32_block_25
  leafTestAt32_block_26)
  (interval_append leafTestAt32 27 28 29
  leafTestAt32_block_27
  leafTestAt32_block_28)))))
cert_leafInterval_2 32 61
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
