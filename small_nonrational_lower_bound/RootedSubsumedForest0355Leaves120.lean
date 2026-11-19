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
cert_leafTestAt 3840
cert_leafTestAt_block_2 3840 0 1
cert_leafTestAt_block_2 3840 1 2
cert_leafTestAt_block_2 3840 2 3
cert_leafTestAt_block_2 3840 3 4
cert_leafTestAt_block_2 3840 4 5
cert_leafTestAt_block_2 3840 5 6
cert_leafTestAt_block_2 3840 6 7
cert_leafTestAt_block_2 3840 7 8
cert_leafTestAt_block_2 3840 8 9
cert_leafTestAt_block_2 3840 9 10
cert_leafTestAt_block_2 3840 10 11
cert_leafTestAt_block_2 3840 11 12
cert_leafTestAt_block_2 3840 12 13
cert_leafTestAt_block_2 3840 13 14
cert_leafTestAt_block_2 3840 14 15
cert_leafTestAt_block_2 3840 15 16
cert_leafTestAt_block_2 3840 16 17
cert_leafTestAt_block_2 3840 17 18
cert_leafTestAt_block_2 3840 18 19
cert_leafTestAt_block_2 3840 19 20
cert_leafTestAt_block_2 3840 20 21
cert_leafTestAt_block_2 3840 21 22
cert_leafTestAt_block_2 3840 22 23
cert_leafTestAt_block_2 3840 23 24
cert_leafTestAt_block_2 3840 24 25
cert_leafTestAt_block_2 3840 25 26
cert_leafTestAt_block_2 3840 26 27
cert_leafTestAt_block_2 3840 27 28
cert_leafTestAt_block_2 3840 28 29
cert_leafTestAt_block_2 3840 29 30
cert_leafTestAt_block_2 3840 30 31
cert_leafTestAt_block_2 3840 31 32
theorem leafTestAt3840_complete : Interval leafTestAt3840 0 32 :=
  (interval_append leafTestAt3840 0 16 32
  (interval_append leafTestAt3840 0 8 16
  (interval_append leafTestAt3840 0 4 8
  (interval_append leafTestAt3840 0 2 4
  (interval_append leafTestAt3840 0 1 2
  leafTestAt3840_block_0
  leafTestAt3840_block_1)
  (interval_append leafTestAt3840 2 3 4
  leafTestAt3840_block_2
  leafTestAt3840_block_3))
  (interval_append leafTestAt3840 4 6 8
  (interval_append leafTestAt3840 4 5 6
  leafTestAt3840_block_4
  leafTestAt3840_block_5)
  (interval_append leafTestAt3840 6 7 8
  leafTestAt3840_block_6
  leafTestAt3840_block_7)))
  (interval_append leafTestAt3840 8 12 16
  (interval_append leafTestAt3840 8 10 12
  (interval_append leafTestAt3840 8 9 10
  leafTestAt3840_block_8
  leafTestAt3840_block_9)
  (interval_append leafTestAt3840 10 11 12
  leafTestAt3840_block_10
  leafTestAt3840_block_11))
  (interval_append leafTestAt3840 12 14 16
  (interval_append leafTestAt3840 12 13 14
  leafTestAt3840_block_12
  leafTestAt3840_block_13)
  (interval_append leafTestAt3840 14 15 16
  leafTestAt3840_block_14
  leafTestAt3840_block_15))))
  (interval_append leafTestAt3840 16 24 32
  (interval_append leafTestAt3840 16 20 24
  (interval_append leafTestAt3840 16 18 20
  (interval_append leafTestAt3840 16 17 18
  leafTestAt3840_block_16
  leafTestAt3840_block_17)
  (interval_append leafTestAt3840 18 19 20
  leafTestAt3840_block_18
  leafTestAt3840_block_19))
  (interval_append leafTestAt3840 20 22 24
  (interval_append leafTestAt3840 20 21 22
  leafTestAt3840_block_20
  leafTestAt3840_block_21)
  (interval_append leafTestAt3840 22 23 24
  leafTestAt3840_block_22
  leafTestAt3840_block_23)))
  (interval_append leafTestAt3840 24 28 32
  (interval_append leafTestAt3840 24 26 28
  (interval_append leafTestAt3840 24 25 26
  leafTestAt3840_block_24
  leafTestAt3840_block_25)
  (interval_append leafTestAt3840 26 27 28
  leafTestAt3840_block_26
  leafTestAt3840_block_27))
  (interval_append leafTestAt3840 28 30 32
  (interval_append leafTestAt3840 28 29 30
  leafTestAt3840_block_28
  leafTestAt3840_block_29)
  (interval_append leafTestAt3840 30 31 32
  leafTestAt3840_block_30
  leafTestAt3840_block_31)))))
cert_leafInterval 3840 3872
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
