module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1152
cert_leafTestAt_block_2 1152 0 1
cert_leafTestAt_block_2 1152 1 2
cert_leafTestAt_block_2 1152 2 3
cert_leafTestAt_block_2 1152 3 4
cert_leafTestAt_block_2 1152 4 5
cert_leafTestAt_block_2 1152 5 6
cert_leafTestAt_block_2 1152 6 7
cert_leafTestAt_block_2 1152 7 8
cert_leafTestAt_block_2 1152 8 9
cert_leafTestAt_block_2 1152 9 10
cert_leafTestAt_block_2 1152 10 11
cert_leafTestAt_block_2 1152 11 12
cert_leafTestAt_block_2 1152 12 13
cert_leafTestAt_block_2 1152 13 14
cert_leafTestAt_block_2 1152 14 15
cert_leafTestAt_block_2 1152 15 16
cert_leafTestAt_block_2 1152 16 17
cert_leafTestAt_block_2 1152 17 18
cert_leafTestAt_block_2 1152 18 19
cert_leafTestAt_block_2 1152 19 20
cert_leafTestAt_block_2 1152 20 21
cert_leafTestAt_block_2 1152 21 22
cert_leafTestAt_block_2 1152 22 23
cert_leafTestAt_block_2 1152 23 24
cert_leafTestAt_block_2 1152 24 25
cert_leafTestAt_block_2 1152 25 26
cert_leafTestAt_block_2 1152 26 27
cert_leafTestAt_block_2 1152 27 28
cert_leafTestAt_block_2 1152 28 29
cert_leafTestAt_block_2 1152 29 30
cert_leafTestAt_block_2 1152 30 31
cert_leafTestAt_block_2 1152 31 32
theorem leafTestAt1152_complete : Interval leafTestAt1152 0 32 :=
  (interval_append leafTestAt1152 0 16 32
  (interval_append leafTestAt1152 0 8 16
  (interval_append leafTestAt1152 0 4 8
  (interval_append leafTestAt1152 0 2 4
  (interval_append leafTestAt1152 0 1 2
  leafTestAt1152_block_0
  leafTestAt1152_block_1)
  (interval_append leafTestAt1152 2 3 4
  leafTestAt1152_block_2
  leafTestAt1152_block_3))
  (interval_append leafTestAt1152 4 6 8
  (interval_append leafTestAt1152 4 5 6
  leafTestAt1152_block_4
  leafTestAt1152_block_5)
  (interval_append leafTestAt1152 6 7 8
  leafTestAt1152_block_6
  leafTestAt1152_block_7)))
  (interval_append leafTestAt1152 8 12 16
  (interval_append leafTestAt1152 8 10 12
  (interval_append leafTestAt1152 8 9 10
  leafTestAt1152_block_8
  leafTestAt1152_block_9)
  (interval_append leafTestAt1152 10 11 12
  leafTestAt1152_block_10
  leafTestAt1152_block_11))
  (interval_append leafTestAt1152 12 14 16
  (interval_append leafTestAt1152 12 13 14
  leafTestAt1152_block_12
  leafTestAt1152_block_13)
  (interval_append leafTestAt1152 14 15 16
  leafTestAt1152_block_14
  leafTestAt1152_block_15))))
  (interval_append leafTestAt1152 16 24 32
  (interval_append leafTestAt1152 16 20 24
  (interval_append leafTestAt1152 16 18 20
  (interval_append leafTestAt1152 16 17 18
  leafTestAt1152_block_16
  leafTestAt1152_block_17)
  (interval_append leafTestAt1152 18 19 20
  leafTestAt1152_block_18
  leafTestAt1152_block_19))
  (interval_append leafTestAt1152 20 22 24
  (interval_append leafTestAt1152 20 21 22
  leafTestAt1152_block_20
  leafTestAt1152_block_21)
  (interval_append leafTestAt1152 22 23 24
  leafTestAt1152_block_22
  leafTestAt1152_block_23)))
  (interval_append leafTestAt1152 24 28 32
  (interval_append leafTestAt1152 24 26 28
  (interval_append leafTestAt1152 24 25 26
  leafTestAt1152_block_24
  leafTestAt1152_block_25)
  (interval_append leafTestAt1152 26 27 28
  leafTestAt1152_block_26
  leafTestAt1152_block_27))
  (interval_append leafTestAt1152 28 30 32
  (interval_append leafTestAt1152 28 29 30
  leafTestAt1152_block_28
  leafTestAt1152_block_29)
  (interval_append leafTestAt1152 30 31 32
  leafTestAt1152_block_30
  leafTestAt1152_block_31)))))
cert_leafInterval 1152 1184
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
