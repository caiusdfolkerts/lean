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
cert_leafTestAt 4032
cert_leafTestAt_block_2 4032 0 1
cert_leafTestAt_block_2 4032 1 2
cert_leafTestAt_block_2 4032 2 3
cert_leafTestAt_block_2 4032 3 4
cert_leafTestAt_block_2 4032 4 5
cert_leafTestAt_block_2 4032 5 6
cert_leafTestAt_block_2 4032 6 7
cert_leafTestAt_block_2 4032 7 8
cert_leafTestAt_block_2 4032 8 9
cert_leafTestAt_block_2 4032 9 10
cert_leafTestAt_block_2 4032 10 11
cert_leafTestAt_block_2 4032 11 12
cert_leafTestAt_block_2 4032 12 13
cert_leafTestAt_block_2 4032 13 14
cert_leafTestAt_block_2 4032 14 15
cert_leafTestAt_block_2 4032 15 16
cert_leafTestAt_block_2 4032 16 17
cert_leafTestAt_block_2 4032 17 18
cert_leafTestAt_block_2 4032 18 19
cert_leafTestAt_block_2 4032 19 20
cert_leafTestAt_block_2 4032 20 21
cert_leafTestAt_block_2 4032 21 22
cert_leafTestAt_block_2 4032 22 23
cert_leafTestAt_block_2 4032 23 24
cert_leafTestAt_block_2 4032 24 25
cert_leafTestAt_block_2 4032 25 26
cert_leafTestAt_block_2 4032 26 27
cert_leafTestAt_block_2 4032 27 28
cert_leafTestAt_block_2 4032 28 29
cert_leafTestAt_block_2 4032 29 30
cert_leafTestAt_block_2 4032 30 31
cert_leafTestAt_block_2 4032 31 32
theorem leafTestAt4032_complete : Interval leafTestAt4032 0 32 :=
  (interval_append leafTestAt4032 0 16 32
  (interval_append leafTestAt4032 0 8 16
  (interval_append leafTestAt4032 0 4 8
  (interval_append leafTestAt4032 0 2 4
  (interval_append leafTestAt4032 0 1 2
  leafTestAt4032_block_0
  leafTestAt4032_block_1)
  (interval_append leafTestAt4032 2 3 4
  leafTestAt4032_block_2
  leafTestAt4032_block_3))
  (interval_append leafTestAt4032 4 6 8
  (interval_append leafTestAt4032 4 5 6
  leafTestAt4032_block_4
  leafTestAt4032_block_5)
  (interval_append leafTestAt4032 6 7 8
  leafTestAt4032_block_6
  leafTestAt4032_block_7)))
  (interval_append leafTestAt4032 8 12 16
  (interval_append leafTestAt4032 8 10 12
  (interval_append leafTestAt4032 8 9 10
  leafTestAt4032_block_8
  leafTestAt4032_block_9)
  (interval_append leafTestAt4032 10 11 12
  leafTestAt4032_block_10
  leafTestAt4032_block_11))
  (interval_append leafTestAt4032 12 14 16
  (interval_append leafTestAt4032 12 13 14
  leafTestAt4032_block_12
  leafTestAt4032_block_13)
  (interval_append leafTestAt4032 14 15 16
  leafTestAt4032_block_14
  leafTestAt4032_block_15))))
  (interval_append leafTestAt4032 16 24 32
  (interval_append leafTestAt4032 16 20 24
  (interval_append leafTestAt4032 16 18 20
  (interval_append leafTestAt4032 16 17 18
  leafTestAt4032_block_16
  leafTestAt4032_block_17)
  (interval_append leafTestAt4032 18 19 20
  leafTestAt4032_block_18
  leafTestAt4032_block_19))
  (interval_append leafTestAt4032 20 22 24
  (interval_append leafTestAt4032 20 21 22
  leafTestAt4032_block_20
  leafTestAt4032_block_21)
  (interval_append leafTestAt4032 22 23 24
  leafTestAt4032_block_22
  leafTestAt4032_block_23)))
  (interval_append leafTestAt4032 24 28 32
  (interval_append leafTestAt4032 24 26 28
  (interval_append leafTestAt4032 24 25 26
  leafTestAt4032_block_24
  leafTestAt4032_block_25)
  (interval_append leafTestAt4032 26 27 28
  leafTestAt4032_block_26
  leafTestAt4032_block_27))
  (interval_append leafTestAt4032 28 30 32
  (interval_append leafTestAt4032 28 29 30
  leafTestAt4032_block_28
  leafTestAt4032_block_29)
  (interval_append leafTestAt4032 30 31 32
  leafTestAt4032_block_30
  leafTestAt4032_block_31)))))
cert_leafInterval 4032 4064
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
