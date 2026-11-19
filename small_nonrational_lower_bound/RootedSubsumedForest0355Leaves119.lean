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
cert_leafTestAt 3808
cert_leafTestAt_block_2 3808 0 1
cert_leafTestAt_block_2 3808 1 2
cert_leafTestAt_block_2 3808 2 3
cert_leafTestAt_block_2 3808 3 4
cert_leafTestAt_block_2 3808 4 5
cert_leafTestAt_block_2 3808 5 6
cert_leafTestAt_block_2 3808 6 7
cert_leafTestAt_block_2 3808 7 8
cert_leafTestAt_block_2 3808 8 9
cert_leafTestAt_block_2 3808 9 10
cert_leafTestAt_block_2 3808 10 11
cert_leafTestAt_block_2 3808 11 12
cert_leafTestAt_block_2 3808 12 13
cert_leafTestAt_block_2 3808 13 14
cert_leafTestAt_block_2 3808 14 15
cert_leafTestAt_block_2 3808 15 16
cert_leafTestAt_block_2 3808 16 17
cert_leafTestAt_block_2 3808 17 18
cert_leafTestAt_block_2 3808 18 19
cert_leafTestAt_block_2 3808 19 20
cert_leafTestAt_block_2 3808 20 21
cert_leafTestAt_block_2 3808 21 22
cert_leafTestAt_block_2 3808 22 23
cert_leafTestAt_block_2 3808 23 24
cert_leafTestAt_block_2 3808 24 25
cert_leafTestAt_block_2 3808 25 26
cert_leafTestAt_block_2 3808 26 27
cert_leafTestAt_block_2 3808 27 28
cert_leafTestAt_block_2 3808 28 29
cert_leafTestAt_block_2 3808 29 30
cert_leafTestAt_block_2 3808 30 31
cert_leafTestAt_block_2 3808 31 32
theorem leafTestAt3808_complete : Interval leafTestAt3808 0 32 :=
  (interval_append leafTestAt3808 0 16 32
  (interval_append leafTestAt3808 0 8 16
  (interval_append leafTestAt3808 0 4 8
  (interval_append leafTestAt3808 0 2 4
  (interval_append leafTestAt3808 0 1 2
  leafTestAt3808_block_0
  leafTestAt3808_block_1)
  (interval_append leafTestAt3808 2 3 4
  leafTestAt3808_block_2
  leafTestAt3808_block_3))
  (interval_append leafTestAt3808 4 6 8
  (interval_append leafTestAt3808 4 5 6
  leafTestAt3808_block_4
  leafTestAt3808_block_5)
  (interval_append leafTestAt3808 6 7 8
  leafTestAt3808_block_6
  leafTestAt3808_block_7)))
  (interval_append leafTestAt3808 8 12 16
  (interval_append leafTestAt3808 8 10 12
  (interval_append leafTestAt3808 8 9 10
  leafTestAt3808_block_8
  leafTestAt3808_block_9)
  (interval_append leafTestAt3808 10 11 12
  leafTestAt3808_block_10
  leafTestAt3808_block_11))
  (interval_append leafTestAt3808 12 14 16
  (interval_append leafTestAt3808 12 13 14
  leafTestAt3808_block_12
  leafTestAt3808_block_13)
  (interval_append leafTestAt3808 14 15 16
  leafTestAt3808_block_14
  leafTestAt3808_block_15))))
  (interval_append leafTestAt3808 16 24 32
  (interval_append leafTestAt3808 16 20 24
  (interval_append leafTestAt3808 16 18 20
  (interval_append leafTestAt3808 16 17 18
  leafTestAt3808_block_16
  leafTestAt3808_block_17)
  (interval_append leafTestAt3808 18 19 20
  leafTestAt3808_block_18
  leafTestAt3808_block_19))
  (interval_append leafTestAt3808 20 22 24
  (interval_append leafTestAt3808 20 21 22
  leafTestAt3808_block_20
  leafTestAt3808_block_21)
  (interval_append leafTestAt3808 22 23 24
  leafTestAt3808_block_22
  leafTestAt3808_block_23)))
  (interval_append leafTestAt3808 24 28 32
  (interval_append leafTestAt3808 24 26 28
  (interval_append leafTestAt3808 24 25 26
  leafTestAt3808_block_24
  leafTestAt3808_block_25)
  (interval_append leafTestAt3808 26 27 28
  leafTestAt3808_block_26
  leafTestAt3808_block_27))
  (interval_append leafTestAt3808 28 30 32
  (interval_append leafTestAt3808 28 29 30
  leafTestAt3808_block_28
  leafTestAt3808_block_29)
  (interval_append leafTestAt3808 30 31 32
  leafTestAt3808_block_30
  leafTestAt3808_block_31)))))
cert_leafInterval 3808 3840
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
