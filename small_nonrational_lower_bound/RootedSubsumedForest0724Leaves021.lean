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
cert_leafTestAt 672
cert_leafTestAt_block_2 672 0 1
cert_leafTestAt_block_2 672 1 2
cert_leafTestAt_block_2 672 2 3
cert_leafTestAt_block_2 672 3 4
cert_leafTestAt_block_2 672 4 5
cert_leafTestAt_block_2 672 5 6
cert_leafTestAt_block_2 672 6 7
cert_leafTestAt_block_2 672 7 8
cert_leafTestAt_block_2 672 8 9
cert_leafTestAt_block_2 672 9 10
cert_leafTestAt_block_2 672 10 11
cert_leafTestAt_block_2 672 11 12
cert_leafTestAt_block_2 672 12 13
cert_leafTestAt_block_2 672 13 14
cert_leafTestAt_block_2 672 14 15
cert_leafTestAt_block_2 672 15 16
cert_leafTestAt_block_2 672 16 17
cert_leafTestAt_block_2 672 17 18
cert_leafTestAt_block_2 672 18 19
cert_leafTestAt_block_2 672 19 20
cert_leafTestAt_block_2 672 20 21
cert_leafTestAt_block_2 672 21 22
cert_leafTestAt_block_2 672 22 23
cert_leafTestAt_block_2 672 23 24
cert_leafTestAt_block_2 672 24 25
cert_leafTestAt_block_2 672 25 26
cert_leafTestAt_block_2 672 26 27
cert_leafTestAt_block_2 672 27 28
cert_leafTestAt_block_2 672 28 29
cert_leafTestAt_block_2 672 29 30
cert_leafTestAt_block_2 672 30 31
cert_leafTestAt_block_2 672 31 32
theorem leafTestAt672_complete : Interval leafTestAt672 0 32 :=
  (interval_append leafTestAt672 0 16 32
  (interval_append leafTestAt672 0 8 16
  (interval_append leafTestAt672 0 4 8
  (interval_append leafTestAt672 0 2 4
  (interval_append leafTestAt672 0 1 2
  leafTestAt672_block_0
  leafTestAt672_block_1)
  (interval_append leafTestAt672 2 3 4
  leafTestAt672_block_2
  leafTestAt672_block_3))
  (interval_append leafTestAt672 4 6 8
  (interval_append leafTestAt672 4 5 6
  leafTestAt672_block_4
  leafTestAt672_block_5)
  (interval_append leafTestAt672 6 7 8
  leafTestAt672_block_6
  leafTestAt672_block_7)))
  (interval_append leafTestAt672 8 12 16
  (interval_append leafTestAt672 8 10 12
  (interval_append leafTestAt672 8 9 10
  leafTestAt672_block_8
  leafTestAt672_block_9)
  (interval_append leafTestAt672 10 11 12
  leafTestAt672_block_10
  leafTestAt672_block_11))
  (interval_append leafTestAt672 12 14 16
  (interval_append leafTestAt672 12 13 14
  leafTestAt672_block_12
  leafTestAt672_block_13)
  (interval_append leafTestAt672 14 15 16
  leafTestAt672_block_14
  leafTestAt672_block_15))))
  (interval_append leafTestAt672 16 24 32
  (interval_append leafTestAt672 16 20 24
  (interval_append leafTestAt672 16 18 20
  (interval_append leafTestAt672 16 17 18
  leafTestAt672_block_16
  leafTestAt672_block_17)
  (interval_append leafTestAt672 18 19 20
  leafTestAt672_block_18
  leafTestAt672_block_19))
  (interval_append leafTestAt672 20 22 24
  (interval_append leafTestAt672 20 21 22
  leafTestAt672_block_20
  leafTestAt672_block_21)
  (interval_append leafTestAt672 22 23 24
  leafTestAt672_block_22
  leafTestAt672_block_23)))
  (interval_append leafTestAt672 24 28 32
  (interval_append leafTestAt672 24 26 28
  (interval_append leafTestAt672 24 25 26
  leafTestAt672_block_24
  leafTestAt672_block_25)
  (interval_append leafTestAt672 26 27 28
  leafTestAt672_block_26
  leafTestAt672_block_27))
  (interval_append leafTestAt672 28 30 32
  (interval_append leafTestAt672 28 29 30
  leafTestAt672_block_28
  leafTestAt672_block_29)
  (interval_append leafTestAt672 30 31 32
  leafTestAt672_block_30
  leafTestAt672_block_31)))))
cert_leafInterval 672 704
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
