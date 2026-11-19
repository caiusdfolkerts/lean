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
cert_leafTestAt 1888
cert_leafTestAt_block_2 1888 0 1
cert_leafTestAt_block_2 1888 1 2
cert_leafTestAt_block_2 1888 2 3
cert_leafTestAt_block_2 1888 3 4
cert_leafTestAt_block_2 1888 4 5
cert_leafTestAt_block_2 1888 5 6
cert_leafTestAt_block_2 1888 6 7
cert_leafTestAt_block_2 1888 7 8
cert_leafTestAt_block_2 1888 8 9
cert_leafTestAt_block_2 1888 9 10
cert_leafTestAt_block_2 1888 10 11
cert_leafTestAt_block_2 1888 11 12
cert_leafTestAt_block_2 1888 12 13
cert_leafTestAt_block_2 1888 13 14
cert_leafTestAt_block_2 1888 14 15
cert_leafTestAt_block_2 1888 15 16
cert_leafTestAt_block_2 1888 16 17
cert_leafTestAt_block_2 1888 17 18
cert_leafTestAt_block_2 1888 18 19
cert_leafTestAt_block_2 1888 19 20
cert_leafTestAt_block_2 1888 20 21
cert_leafTestAt_block_2 1888 21 22
cert_leafTestAt_block_2 1888 22 23
cert_leafTestAt_block_2 1888 23 24
cert_leafTestAt_block_2 1888 24 25
cert_leafTestAt_block_2 1888 25 26
cert_leafTestAt_block_2 1888 26 27
cert_leafTestAt_block_2 1888 27 28
cert_leafTestAt_block_2 1888 28 29
cert_leafTestAt_block_2 1888 29 30
cert_leafTestAt_block_2 1888 30 31
cert_leafTestAt_block_2 1888 31 32
theorem leafTestAt1888_complete : Interval leafTestAt1888 0 32 :=
  (interval_append leafTestAt1888 0 16 32
  (interval_append leafTestAt1888 0 8 16
  (interval_append leafTestAt1888 0 4 8
  (interval_append leafTestAt1888 0 2 4
  (interval_append leafTestAt1888 0 1 2
  leafTestAt1888_block_0
  leafTestAt1888_block_1)
  (interval_append leafTestAt1888 2 3 4
  leafTestAt1888_block_2
  leafTestAt1888_block_3))
  (interval_append leafTestAt1888 4 6 8
  (interval_append leafTestAt1888 4 5 6
  leafTestAt1888_block_4
  leafTestAt1888_block_5)
  (interval_append leafTestAt1888 6 7 8
  leafTestAt1888_block_6
  leafTestAt1888_block_7)))
  (interval_append leafTestAt1888 8 12 16
  (interval_append leafTestAt1888 8 10 12
  (interval_append leafTestAt1888 8 9 10
  leafTestAt1888_block_8
  leafTestAt1888_block_9)
  (interval_append leafTestAt1888 10 11 12
  leafTestAt1888_block_10
  leafTestAt1888_block_11))
  (interval_append leafTestAt1888 12 14 16
  (interval_append leafTestAt1888 12 13 14
  leafTestAt1888_block_12
  leafTestAt1888_block_13)
  (interval_append leafTestAt1888 14 15 16
  leafTestAt1888_block_14
  leafTestAt1888_block_15))))
  (interval_append leafTestAt1888 16 24 32
  (interval_append leafTestAt1888 16 20 24
  (interval_append leafTestAt1888 16 18 20
  (interval_append leafTestAt1888 16 17 18
  leafTestAt1888_block_16
  leafTestAt1888_block_17)
  (interval_append leafTestAt1888 18 19 20
  leafTestAt1888_block_18
  leafTestAt1888_block_19))
  (interval_append leafTestAt1888 20 22 24
  (interval_append leafTestAt1888 20 21 22
  leafTestAt1888_block_20
  leafTestAt1888_block_21)
  (interval_append leafTestAt1888 22 23 24
  leafTestAt1888_block_22
  leafTestAt1888_block_23)))
  (interval_append leafTestAt1888 24 28 32
  (interval_append leafTestAt1888 24 26 28
  (interval_append leafTestAt1888 24 25 26
  leafTestAt1888_block_24
  leafTestAt1888_block_25)
  (interval_append leafTestAt1888 26 27 28
  leafTestAt1888_block_26
  leafTestAt1888_block_27))
  (interval_append leafTestAt1888 28 30 32
  (interval_append leafTestAt1888 28 29 30
  leafTestAt1888_block_28
  leafTestAt1888_block_29)
  (interval_append leafTestAt1888 30 31 32
  leafTestAt1888_block_30
  leafTestAt1888_block_31)))))
cert_leafInterval 1888 1920
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
