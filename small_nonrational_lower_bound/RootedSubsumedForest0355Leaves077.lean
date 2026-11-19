module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0355Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2464
cert_leafTestAt_block_2 2464 0 1
cert_leafTestAt_block_2 2464 1 2
cert_leafTestAt_block_2 2464 2 3
cert_leafTestAt_block_2 2464 3 4
cert_leafTestAt_block_2 2464 4 5
cert_leafTestAt_block_2 2464 5 6
cert_leafTestAt_block_2 2464 6 7
cert_leafTestAt_block_2 2464 7 8
cert_leafTestAt_block_2 2464 8 9
cert_leafTestAt_block_2 2464 9 10
cert_leafTestAt_block_2 2464 10 11
cert_leafTestAt_block_2 2464 11 12
cert_leafTestAt_block_2 2464 12 13
cert_leafTestAt_block_2 2464 13 14
cert_leafTestAt_block_2 2464 14 15
cert_leafTestAt_block_2 2464 15 16
cert_leafTestAt_block_2 2464 16 17
cert_leafTestAt_block_2 2464 17 18
cert_leafTestAt_block_2 2464 18 19
cert_leafTestAt_block_2 2464 19 20
cert_leafTestAt_block_2 2464 20 21
cert_leafTestAt_block_2 2464 21 22
cert_leafTestAt_block_2 2464 22 23
cert_leafTestAt_block_2 2464 23 24
cert_leafTestAt_block_2 2464 24 25
cert_leafTestAt_block_2 2464 25 26
cert_leafTestAt_block_2 2464 26 27
cert_leafTestAt_block_2 2464 27 28
cert_leafTestAt_block_2 2464 28 29
cert_leafTestAt_block_2 2464 29 30
cert_leafTestAt_block_2 2464 30 31
cert_leafTestAt_block_2 2464 31 32
theorem leafTestAt2464_complete : Interval leafTestAt2464 0 32 :=
  (interval_append leafTestAt2464 0 16 32
  (interval_append leafTestAt2464 0 8 16
  (interval_append leafTestAt2464 0 4 8
  (interval_append leafTestAt2464 0 2 4
  (interval_append leafTestAt2464 0 1 2
  leafTestAt2464_block_0
  leafTestAt2464_block_1)
  (interval_append leafTestAt2464 2 3 4
  leafTestAt2464_block_2
  leafTestAt2464_block_3))
  (interval_append leafTestAt2464 4 6 8
  (interval_append leafTestAt2464 4 5 6
  leafTestAt2464_block_4
  leafTestAt2464_block_5)
  (interval_append leafTestAt2464 6 7 8
  leafTestAt2464_block_6
  leafTestAt2464_block_7)))
  (interval_append leafTestAt2464 8 12 16
  (interval_append leafTestAt2464 8 10 12
  (interval_append leafTestAt2464 8 9 10
  leafTestAt2464_block_8
  leafTestAt2464_block_9)
  (interval_append leafTestAt2464 10 11 12
  leafTestAt2464_block_10
  leafTestAt2464_block_11))
  (interval_append leafTestAt2464 12 14 16
  (interval_append leafTestAt2464 12 13 14
  leafTestAt2464_block_12
  leafTestAt2464_block_13)
  (interval_append leafTestAt2464 14 15 16
  leafTestAt2464_block_14
  leafTestAt2464_block_15))))
  (interval_append leafTestAt2464 16 24 32
  (interval_append leafTestAt2464 16 20 24
  (interval_append leafTestAt2464 16 18 20
  (interval_append leafTestAt2464 16 17 18
  leafTestAt2464_block_16
  leafTestAt2464_block_17)
  (interval_append leafTestAt2464 18 19 20
  leafTestAt2464_block_18
  leafTestAt2464_block_19))
  (interval_append leafTestAt2464 20 22 24
  (interval_append leafTestAt2464 20 21 22
  leafTestAt2464_block_20
  leafTestAt2464_block_21)
  (interval_append leafTestAt2464 22 23 24
  leafTestAt2464_block_22
  leafTestAt2464_block_23)))
  (interval_append leafTestAt2464 24 28 32
  (interval_append leafTestAt2464 24 26 28
  (interval_append leafTestAt2464 24 25 26
  leafTestAt2464_block_24
  leafTestAt2464_block_25)
  (interval_append leafTestAt2464 26 27 28
  leafTestAt2464_block_26
  leafTestAt2464_block_27))
  (interval_append leafTestAt2464 28 30 32
  (interval_append leafTestAt2464 28 29 30
  leafTestAt2464_block_28
  leafTestAt2464_block_29)
  (interval_append leafTestAt2464 30 31 32
  leafTestAt2464_block_30
  leafTestAt2464_block_31)))))
cert_leafInterval 2464 2496
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
