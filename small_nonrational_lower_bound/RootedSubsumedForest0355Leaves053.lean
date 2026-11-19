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
cert_leafTestAt 1696
cert_leafTestAt_block_2 1696 0 1
cert_leafTestAt_block_2 1696 1 2
cert_leafTestAt_block_2 1696 2 3
cert_leafTestAt_block_2 1696 3 4
cert_leafTestAt_block_2 1696 4 5
cert_leafTestAt_block_2 1696 5 6
cert_leafTestAt_block_2 1696 6 7
cert_leafTestAt_block_2 1696 7 8
cert_leafTestAt_block_2 1696 8 9
cert_leafTestAt_block_2 1696 9 10
cert_leafTestAt_block_2 1696 10 11
cert_leafTestAt_block_2 1696 11 12
cert_leafTestAt_block_2 1696 12 13
cert_leafTestAt_block_2 1696 13 14
cert_leafTestAt_block_2 1696 14 15
cert_leafTestAt_block_2 1696 15 16
cert_leafTestAt_block_2 1696 16 17
cert_leafTestAt_block_2 1696 17 18
cert_leafTestAt_block_2 1696 18 19
cert_leafTestAt_block_2 1696 19 20
cert_leafTestAt_block_2 1696 20 21
cert_leafTestAt_block_2 1696 21 22
cert_leafTestAt_block_2 1696 22 23
cert_leafTestAt_block_2 1696 23 24
cert_leafTestAt_block_2 1696 24 25
cert_leafTestAt_block_2 1696 25 26
cert_leafTestAt_block_2 1696 26 27
cert_leafTestAt_block_2 1696 27 28
cert_leafTestAt_block_2 1696 28 29
cert_leafTestAt_block_2 1696 29 30
cert_leafTestAt_block_2 1696 30 31
cert_leafTestAt_block_2 1696 31 32
theorem leafTestAt1696_complete : Interval leafTestAt1696 0 32 :=
  (interval_append leafTestAt1696 0 16 32
  (interval_append leafTestAt1696 0 8 16
  (interval_append leafTestAt1696 0 4 8
  (interval_append leafTestAt1696 0 2 4
  (interval_append leafTestAt1696 0 1 2
  leafTestAt1696_block_0
  leafTestAt1696_block_1)
  (interval_append leafTestAt1696 2 3 4
  leafTestAt1696_block_2
  leafTestAt1696_block_3))
  (interval_append leafTestAt1696 4 6 8
  (interval_append leafTestAt1696 4 5 6
  leafTestAt1696_block_4
  leafTestAt1696_block_5)
  (interval_append leafTestAt1696 6 7 8
  leafTestAt1696_block_6
  leafTestAt1696_block_7)))
  (interval_append leafTestAt1696 8 12 16
  (interval_append leafTestAt1696 8 10 12
  (interval_append leafTestAt1696 8 9 10
  leafTestAt1696_block_8
  leafTestAt1696_block_9)
  (interval_append leafTestAt1696 10 11 12
  leafTestAt1696_block_10
  leafTestAt1696_block_11))
  (interval_append leafTestAt1696 12 14 16
  (interval_append leafTestAt1696 12 13 14
  leafTestAt1696_block_12
  leafTestAt1696_block_13)
  (interval_append leafTestAt1696 14 15 16
  leafTestAt1696_block_14
  leafTestAt1696_block_15))))
  (interval_append leafTestAt1696 16 24 32
  (interval_append leafTestAt1696 16 20 24
  (interval_append leafTestAt1696 16 18 20
  (interval_append leafTestAt1696 16 17 18
  leafTestAt1696_block_16
  leafTestAt1696_block_17)
  (interval_append leafTestAt1696 18 19 20
  leafTestAt1696_block_18
  leafTestAt1696_block_19))
  (interval_append leafTestAt1696 20 22 24
  (interval_append leafTestAt1696 20 21 22
  leafTestAt1696_block_20
  leafTestAt1696_block_21)
  (interval_append leafTestAt1696 22 23 24
  leafTestAt1696_block_22
  leafTestAt1696_block_23)))
  (interval_append leafTestAt1696 24 28 32
  (interval_append leafTestAt1696 24 26 28
  (interval_append leafTestAt1696 24 25 26
  leafTestAt1696_block_24
  leafTestAt1696_block_25)
  (interval_append leafTestAt1696 26 27 28
  leafTestAt1696_block_26
  leafTestAt1696_block_27))
  (interval_append leafTestAt1696 28 30 32
  (interval_append leafTestAt1696 28 29 30
  leafTestAt1696_block_28
  leafTestAt1696_block_29)
  (interval_append leafTestAt1696 30 31 32
  leafTestAt1696_block_30
  leafTestAt1696_block_31)))))
cert_leafInterval 1696 1728
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
