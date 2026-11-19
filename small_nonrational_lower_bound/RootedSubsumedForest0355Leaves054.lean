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
cert_leafTestAt 1728
cert_leafTestAt_block_2 1728 0 1
cert_leafTestAt_block_2 1728 1 2
cert_leafTestAt_block_2 1728 2 3
cert_leafTestAt_block_2 1728 3 4
cert_leafTestAt_block_2 1728 4 5
cert_leafTestAt_block_2 1728 5 6
cert_leafTestAt_block_2 1728 6 7
cert_leafTestAt_block_2 1728 7 8
cert_leafTestAt_block_2 1728 8 9
cert_leafTestAt_block_2 1728 9 10
cert_leafTestAt_block_2 1728 10 11
cert_leafTestAt_block_2 1728 11 12
cert_leafTestAt_block_2 1728 12 13
cert_leafTestAt_block_2 1728 13 14
cert_leafTestAt_block_2 1728 14 15
cert_leafTestAt_block_2 1728 15 16
cert_leafTestAt_block_2 1728 16 17
cert_leafTestAt_block_2 1728 17 18
cert_leafTestAt_block_2 1728 18 19
cert_leafTestAt_block_2 1728 19 20
cert_leafTestAt_block_2 1728 20 21
cert_leafTestAt_block_2 1728 21 22
cert_leafTestAt_block_2 1728 22 23
cert_leafTestAt_block_2 1728 23 24
cert_leafTestAt_block_2 1728 24 25
cert_leafTestAt_block_2 1728 25 26
cert_leafTestAt_block_2 1728 26 27
cert_leafTestAt_block_2 1728 27 28
cert_leafTestAt_block_2 1728 28 29
cert_leafTestAt_block_2 1728 29 30
cert_leafTestAt_block_2 1728 30 31
cert_leafTestAt_block_2 1728 31 32
theorem leafTestAt1728_complete : Interval leafTestAt1728 0 32 :=
  (interval_append leafTestAt1728 0 16 32
  (interval_append leafTestAt1728 0 8 16
  (interval_append leafTestAt1728 0 4 8
  (interval_append leafTestAt1728 0 2 4
  (interval_append leafTestAt1728 0 1 2
  leafTestAt1728_block_0
  leafTestAt1728_block_1)
  (interval_append leafTestAt1728 2 3 4
  leafTestAt1728_block_2
  leafTestAt1728_block_3))
  (interval_append leafTestAt1728 4 6 8
  (interval_append leafTestAt1728 4 5 6
  leafTestAt1728_block_4
  leafTestAt1728_block_5)
  (interval_append leafTestAt1728 6 7 8
  leafTestAt1728_block_6
  leafTestAt1728_block_7)))
  (interval_append leafTestAt1728 8 12 16
  (interval_append leafTestAt1728 8 10 12
  (interval_append leafTestAt1728 8 9 10
  leafTestAt1728_block_8
  leafTestAt1728_block_9)
  (interval_append leafTestAt1728 10 11 12
  leafTestAt1728_block_10
  leafTestAt1728_block_11))
  (interval_append leafTestAt1728 12 14 16
  (interval_append leafTestAt1728 12 13 14
  leafTestAt1728_block_12
  leafTestAt1728_block_13)
  (interval_append leafTestAt1728 14 15 16
  leafTestAt1728_block_14
  leafTestAt1728_block_15))))
  (interval_append leafTestAt1728 16 24 32
  (interval_append leafTestAt1728 16 20 24
  (interval_append leafTestAt1728 16 18 20
  (interval_append leafTestAt1728 16 17 18
  leafTestAt1728_block_16
  leafTestAt1728_block_17)
  (interval_append leafTestAt1728 18 19 20
  leafTestAt1728_block_18
  leafTestAt1728_block_19))
  (interval_append leafTestAt1728 20 22 24
  (interval_append leafTestAt1728 20 21 22
  leafTestAt1728_block_20
  leafTestAt1728_block_21)
  (interval_append leafTestAt1728 22 23 24
  leafTestAt1728_block_22
  leafTestAt1728_block_23)))
  (interval_append leafTestAt1728 24 28 32
  (interval_append leafTestAt1728 24 26 28
  (interval_append leafTestAt1728 24 25 26
  leafTestAt1728_block_24
  leafTestAt1728_block_25)
  (interval_append leafTestAt1728 26 27 28
  leafTestAt1728_block_26
  leafTestAt1728_block_27))
  (interval_append leafTestAt1728 28 30 32
  (interval_append leafTestAt1728 28 29 30
  leafTestAt1728_block_28
  leafTestAt1728_block_29)
  (interval_append leafTestAt1728 30 31 32
  leafTestAt1728_block_30
  leafTestAt1728_block_31)))))
cert_leafInterval 1728 1760
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
