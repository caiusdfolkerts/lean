module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2368
cert_leafTestAt_block_2 2368 0 1
cert_leafTestAt_block_2 2368 1 2
cert_leafTestAt_block_2 2368 2 3
cert_leafTestAt_block_2 2368 3 4
cert_leafTestAt_block_2 2368 4 5
cert_leafTestAt_block_2 2368 5 6
cert_leafTestAt_block_2 2368 6 7
cert_leafTestAt_block_2 2368 7 8
cert_leafTestAt_block_2 2368 8 9
cert_leafTestAt_block_2 2368 9 10
cert_leafTestAt_block_2 2368 10 11
cert_leafTestAt_block_2 2368 11 12
cert_leafTestAt_block_2 2368 12 13
cert_leafTestAt_block_2 2368 13 14
cert_leafTestAt_block_2 2368 14 15
cert_leafTestAt_block_2 2368 15 16
cert_leafTestAt_block_2 2368 16 17
cert_leafTestAt_block_2 2368 17 18
cert_leafTestAt_block_2 2368 18 19
cert_leafTestAt_block_2 2368 19 20
cert_leafTestAt_block_2 2368 20 21
cert_leafTestAt_block_2 2368 21 22
cert_leafTestAt_block_2 2368 22 23
cert_leafTestAt_block_2 2368 23 24
cert_leafTestAt_block_2 2368 24 25
cert_leafTestAt_block_2 2368 25 26
cert_leafTestAt_block_2 2368 26 27
cert_leafTestAt_block_2 2368 27 28
cert_leafTestAt_block_2 2368 28 29
cert_leafTestAt_block_2 2368 29 30
cert_leafTestAt_block_2 2368 30 31
cert_leafTestAt_block_2 2368 31 32
theorem leafTestAt2368_complete : Interval leafTestAt2368 0 32 :=
  (interval_append leafTestAt2368 0 16 32
  (interval_append leafTestAt2368 0 8 16
  (interval_append leafTestAt2368 0 4 8
  (interval_append leafTestAt2368 0 2 4
  (interval_append leafTestAt2368 0 1 2
  leafTestAt2368_block_0
  leafTestAt2368_block_1)
  (interval_append leafTestAt2368 2 3 4
  leafTestAt2368_block_2
  leafTestAt2368_block_3))
  (interval_append leafTestAt2368 4 6 8
  (interval_append leafTestAt2368 4 5 6
  leafTestAt2368_block_4
  leafTestAt2368_block_5)
  (interval_append leafTestAt2368 6 7 8
  leafTestAt2368_block_6
  leafTestAt2368_block_7)))
  (interval_append leafTestAt2368 8 12 16
  (interval_append leafTestAt2368 8 10 12
  (interval_append leafTestAt2368 8 9 10
  leafTestAt2368_block_8
  leafTestAt2368_block_9)
  (interval_append leafTestAt2368 10 11 12
  leafTestAt2368_block_10
  leafTestAt2368_block_11))
  (interval_append leafTestAt2368 12 14 16
  (interval_append leafTestAt2368 12 13 14
  leafTestAt2368_block_12
  leafTestAt2368_block_13)
  (interval_append leafTestAt2368 14 15 16
  leafTestAt2368_block_14
  leafTestAt2368_block_15))))
  (interval_append leafTestAt2368 16 24 32
  (interval_append leafTestAt2368 16 20 24
  (interval_append leafTestAt2368 16 18 20
  (interval_append leafTestAt2368 16 17 18
  leafTestAt2368_block_16
  leafTestAt2368_block_17)
  (interval_append leafTestAt2368 18 19 20
  leafTestAt2368_block_18
  leafTestAt2368_block_19))
  (interval_append leafTestAt2368 20 22 24
  (interval_append leafTestAt2368 20 21 22
  leafTestAt2368_block_20
  leafTestAt2368_block_21)
  (interval_append leafTestAt2368 22 23 24
  leafTestAt2368_block_22
  leafTestAt2368_block_23)))
  (interval_append leafTestAt2368 24 28 32
  (interval_append leafTestAt2368 24 26 28
  (interval_append leafTestAt2368 24 25 26
  leafTestAt2368_block_24
  leafTestAt2368_block_25)
  (interval_append leafTestAt2368 26 27 28
  leafTestAt2368_block_26
  leafTestAt2368_block_27))
  (interval_append leafTestAt2368 28 30 32
  (interval_append leafTestAt2368 28 29 30
  leafTestAt2368_block_28
  leafTestAt2368_block_29)
  (interval_append leafTestAt2368 30 31 32
  leafTestAt2368_block_30
  leafTestAt2368_block_31)))))
cert_leafInterval 2368 2400
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
