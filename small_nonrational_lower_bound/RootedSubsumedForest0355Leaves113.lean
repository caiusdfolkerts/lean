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
cert_leafTestAt 3616
cert_leafTestAt_block_2 3616 0 1
cert_leafTestAt_block_2 3616 1 2
cert_leafTestAt_block_2 3616 2 3
cert_leafTestAt_block_2 3616 3 4
cert_leafTestAt_block_2 3616 4 5
cert_leafTestAt_block_2 3616 5 6
cert_leafTestAt_block_2 3616 6 7
cert_leafTestAt_block_2 3616 7 8
cert_leafTestAt_block_2 3616 8 9
cert_leafTestAt_block_2 3616 9 10
cert_leafTestAt_block_2 3616 10 11
cert_leafTestAt_block_2 3616 11 12
cert_leafTestAt_block_2 3616 12 13
cert_leafTestAt_block_2 3616 13 14
cert_leafTestAt_block_2 3616 14 15
cert_leafTestAt_block_2 3616 15 16
cert_leafTestAt_block_2 3616 16 17
cert_leafTestAt_block_2 3616 17 18
cert_leafTestAt_block_2 3616 18 19
cert_leafTestAt_block_2 3616 19 20
cert_leafTestAt_block_2 3616 20 21
cert_leafTestAt_block_2 3616 21 22
cert_leafTestAt_block_2 3616 22 23
cert_leafTestAt_block_2 3616 23 24
cert_leafTestAt_block_2 3616 24 25
cert_leafTestAt_block_2 3616 25 26
cert_leafTestAt_block_2 3616 26 27
cert_leafTestAt_block_2 3616 27 28
cert_leafTestAt_block_2 3616 28 29
cert_leafTestAt_block_2 3616 29 30
cert_leafTestAt_block_2 3616 30 31
cert_leafTestAt_block_2 3616 31 32
theorem leafTestAt3616_complete : Interval leafTestAt3616 0 32 :=
  (interval_append leafTestAt3616 0 16 32
  (interval_append leafTestAt3616 0 8 16
  (interval_append leafTestAt3616 0 4 8
  (interval_append leafTestAt3616 0 2 4
  (interval_append leafTestAt3616 0 1 2
  leafTestAt3616_block_0
  leafTestAt3616_block_1)
  (interval_append leafTestAt3616 2 3 4
  leafTestAt3616_block_2
  leafTestAt3616_block_3))
  (interval_append leafTestAt3616 4 6 8
  (interval_append leafTestAt3616 4 5 6
  leafTestAt3616_block_4
  leafTestAt3616_block_5)
  (interval_append leafTestAt3616 6 7 8
  leafTestAt3616_block_6
  leafTestAt3616_block_7)))
  (interval_append leafTestAt3616 8 12 16
  (interval_append leafTestAt3616 8 10 12
  (interval_append leafTestAt3616 8 9 10
  leafTestAt3616_block_8
  leafTestAt3616_block_9)
  (interval_append leafTestAt3616 10 11 12
  leafTestAt3616_block_10
  leafTestAt3616_block_11))
  (interval_append leafTestAt3616 12 14 16
  (interval_append leafTestAt3616 12 13 14
  leafTestAt3616_block_12
  leafTestAt3616_block_13)
  (interval_append leafTestAt3616 14 15 16
  leafTestAt3616_block_14
  leafTestAt3616_block_15))))
  (interval_append leafTestAt3616 16 24 32
  (interval_append leafTestAt3616 16 20 24
  (interval_append leafTestAt3616 16 18 20
  (interval_append leafTestAt3616 16 17 18
  leafTestAt3616_block_16
  leafTestAt3616_block_17)
  (interval_append leafTestAt3616 18 19 20
  leafTestAt3616_block_18
  leafTestAt3616_block_19))
  (interval_append leafTestAt3616 20 22 24
  (interval_append leafTestAt3616 20 21 22
  leafTestAt3616_block_20
  leafTestAt3616_block_21)
  (interval_append leafTestAt3616 22 23 24
  leafTestAt3616_block_22
  leafTestAt3616_block_23)))
  (interval_append leafTestAt3616 24 28 32
  (interval_append leafTestAt3616 24 26 28
  (interval_append leafTestAt3616 24 25 26
  leafTestAt3616_block_24
  leafTestAt3616_block_25)
  (interval_append leafTestAt3616 26 27 28
  leafTestAt3616_block_26
  leafTestAt3616_block_27))
  (interval_append leafTestAt3616 28 30 32
  (interval_append leafTestAt3616 28 29 30
  leafTestAt3616_block_28
  leafTestAt3616_block_29)
  (interval_append leafTestAt3616 30 31 32
  leafTestAt3616_block_30
  leafTestAt3616_block_31)))))
cert_leafInterval 3616 3648
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
