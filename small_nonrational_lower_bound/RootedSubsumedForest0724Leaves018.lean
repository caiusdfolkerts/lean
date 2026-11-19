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
cert_leafTestAt 576
cert_leafTestAt_block_2 576 0 1
cert_leafTestAt_block_2 576 1 2
cert_leafTestAt_block_2 576 2 3
cert_leafTestAt_block_2 576 3 4
cert_leafTestAt_block_2 576 4 5
cert_leafTestAt_block_2 576 5 6
cert_leafTestAt_block_2 576 6 7
cert_leafTestAt_block_2 576 7 8
cert_leafTestAt_block_2 576 8 9
cert_leafTestAt_block_2 576 9 10
cert_leafTestAt_block_2 576 10 11
cert_leafTestAt_block_2 576 11 12
cert_leafTestAt_block_2 576 12 13
cert_leafTestAt_block_2 576 13 14
cert_leafTestAt_block_2 576 14 15
cert_leafTestAt_block_2 576 15 16
cert_leafTestAt_block_2 576 16 17
cert_leafTestAt_block_2 576 17 18
cert_leafTestAt_block_2 576 18 19
cert_leafTestAt_block_2 576 19 20
cert_leafTestAt_block_2 576 20 21
cert_leafTestAt_block_2 576 21 22
cert_leafTestAt_block_2 576 22 23
cert_leafTestAt_block_2 576 23 24
cert_leafTestAt_block_2 576 24 25
cert_leafTestAt_block_2 576 25 26
cert_leafTestAt_block_2 576 26 27
cert_leafTestAt_block_2 576 27 28
cert_leafTestAt_block_2 576 28 29
cert_leafTestAt_block_2 576 29 30
cert_leafTestAt_block_2 576 30 31
cert_leafTestAt_block_2 576 31 32
theorem leafTestAt576_complete : Interval leafTestAt576 0 32 :=
  (interval_append leafTestAt576 0 16 32
  (interval_append leafTestAt576 0 8 16
  (interval_append leafTestAt576 0 4 8
  (interval_append leafTestAt576 0 2 4
  (interval_append leafTestAt576 0 1 2
  leafTestAt576_block_0
  leafTestAt576_block_1)
  (interval_append leafTestAt576 2 3 4
  leafTestAt576_block_2
  leafTestAt576_block_3))
  (interval_append leafTestAt576 4 6 8
  (interval_append leafTestAt576 4 5 6
  leafTestAt576_block_4
  leafTestAt576_block_5)
  (interval_append leafTestAt576 6 7 8
  leafTestAt576_block_6
  leafTestAt576_block_7)))
  (interval_append leafTestAt576 8 12 16
  (interval_append leafTestAt576 8 10 12
  (interval_append leafTestAt576 8 9 10
  leafTestAt576_block_8
  leafTestAt576_block_9)
  (interval_append leafTestAt576 10 11 12
  leafTestAt576_block_10
  leafTestAt576_block_11))
  (interval_append leafTestAt576 12 14 16
  (interval_append leafTestAt576 12 13 14
  leafTestAt576_block_12
  leafTestAt576_block_13)
  (interval_append leafTestAt576 14 15 16
  leafTestAt576_block_14
  leafTestAt576_block_15))))
  (interval_append leafTestAt576 16 24 32
  (interval_append leafTestAt576 16 20 24
  (interval_append leafTestAt576 16 18 20
  (interval_append leafTestAt576 16 17 18
  leafTestAt576_block_16
  leafTestAt576_block_17)
  (interval_append leafTestAt576 18 19 20
  leafTestAt576_block_18
  leafTestAt576_block_19))
  (interval_append leafTestAt576 20 22 24
  (interval_append leafTestAt576 20 21 22
  leafTestAt576_block_20
  leafTestAt576_block_21)
  (interval_append leafTestAt576 22 23 24
  leafTestAt576_block_22
  leafTestAt576_block_23)))
  (interval_append leafTestAt576 24 28 32
  (interval_append leafTestAt576 24 26 28
  (interval_append leafTestAt576 24 25 26
  leafTestAt576_block_24
  leafTestAt576_block_25)
  (interval_append leafTestAt576 26 27 28
  leafTestAt576_block_26
  leafTestAt576_block_27))
  (interval_append leafTestAt576 28 30 32
  (interval_append leafTestAt576 28 29 30
  leafTestAt576_block_28
  leafTestAt576_block_29)
  (interval_append leafTestAt576 30 31 32
  leafTestAt576_block_30
  leafTestAt576_block_31)))))
cert_leafInterval 576 608
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
