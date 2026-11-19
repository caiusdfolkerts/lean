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
cert_leafTestAt 1600
cert_leafTestAt_block_2 1600 0 1
cert_leafTestAt_block_2 1600 1 2
cert_leafTestAt_block_2 1600 2 3
cert_leafTestAt_block_2 1600 3 4
cert_leafTestAt_block_2 1600 4 5
cert_leafTestAt_block_2 1600 5 6
cert_leafTestAt_block_2 1600 6 7
cert_leafTestAt_block_2 1600 7 8
cert_leafTestAt_block_2 1600 8 9
cert_leafTestAt_block_2 1600 9 10
cert_leafTestAt_block_2 1600 10 11
cert_leafTestAt_block_2 1600 11 12
cert_leafTestAt_block_2 1600 12 13
cert_leafTestAt_block_2 1600 13 14
cert_leafTestAt_block_2 1600 14 15
cert_leafTestAt_block_2 1600 15 16
cert_leafTestAt_block_2 1600 16 17
cert_leafTestAt_block_2 1600 17 18
cert_leafTestAt_block_2 1600 18 19
cert_leafTestAt_block_2 1600 19 20
cert_leafTestAt_block_2 1600 20 21
cert_leafTestAt_block_2 1600 21 22
cert_leafTestAt_block_2 1600 22 23
cert_leafTestAt_block_2 1600 23 24
cert_leafTestAt_block_2 1600 24 25
cert_leafTestAt_block_2 1600 25 26
cert_leafTestAt_block_2 1600 26 27
cert_leafTestAt_block_2 1600 27 28
cert_leafTestAt_block_2 1600 28 29
cert_leafTestAt_block_2 1600 29 30
cert_leafTestAt_block_2 1600 30 31
cert_leafTestAt_block_2 1600 31 32
theorem leafTestAt1600_complete : Interval leafTestAt1600 0 32 :=
  (interval_append leafTestAt1600 0 16 32
  (interval_append leafTestAt1600 0 8 16
  (interval_append leafTestAt1600 0 4 8
  (interval_append leafTestAt1600 0 2 4
  (interval_append leafTestAt1600 0 1 2
  leafTestAt1600_block_0
  leafTestAt1600_block_1)
  (interval_append leafTestAt1600 2 3 4
  leafTestAt1600_block_2
  leafTestAt1600_block_3))
  (interval_append leafTestAt1600 4 6 8
  (interval_append leafTestAt1600 4 5 6
  leafTestAt1600_block_4
  leafTestAt1600_block_5)
  (interval_append leafTestAt1600 6 7 8
  leafTestAt1600_block_6
  leafTestAt1600_block_7)))
  (interval_append leafTestAt1600 8 12 16
  (interval_append leafTestAt1600 8 10 12
  (interval_append leafTestAt1600 8 9 10
  leafTestAt1600_block_8
  leafTestAt1600_block_9)
  (interval_append leafTestAt1600 10 11 12
  leafTestAt1600_block_10
  leafTestAt1600_block_11))
  (interval_append leafTestAt1600 12 14 16
  (interval_append leafTestAt1600 12 13 14
  leafTestAt1600_block_12
  leafTestAt1600_block_13)
  (interval_append leafTestAt1600 14 15 16
  leafTestAt1600_block_14
  leafTestAt1600_block_15))))
  (interval_append leafTestAt1600 16 24 32
  (interval_append leafTestAt1600 16 20 24
  (interval_append leafTestAt1600 16 18 20
  (interval_append leafTestAt1600 16 17 18
  leafTestAt1600_block_16
  leafTestAt1600_block_17)
  (interval_append leafTestAt1600 18 19 20
  leafTestAt1600_block_18
  leafTestAt1600_block_19))
  (interval_append leafTestAt1600 20 22 24
  (interval_append leafTestAt1600 20 21 22
  leafTestAt1600_block_20
  leafTestAt1600_block_21)
  (interval_append leafTestAt1600 22 23 24
  leafTestAt1600_block_22
  leafTestAt1600_block_23)))
  (interval_append leafTestAt1600 24 28 32
  (interval_append leafTestAt1600 24 26 28
  (interval_append leafTestAt1600 24 25 26
  leafTestAt1600_block_24
  leafTestAt1600_block_25)
  (interval_append leafTestAt1600 26 27 28
  leafTestAt1600_block_26
  leafTestAt1600_block_27))
  (interval_append leafTestAt1600 28 30 32
  (interval_append leafTestAt1600 28 29 30
  leafTestAt1600_block_28
  leafTestAt1600_block_29)
  (interval_append leafTestAt1600 30 31 32
  leafTestAt1600_block_30
  leafTestAt1600_block_31)))))
cert_leafInterval 1600 1632
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
