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
cert_leafTestAt 864
cert_leafTestAt_block_2 864 0 1
cert_leafTestAt_block_2 864 1 2
cert_leafTestAt_block_2 864 2 3
cert_leafTestAt_block_2 864 3 4
cert_leafTestAt_block_2 864 4 5
cert_leafTestAt_block_2 864 5 6
cert_leafTestAt_block_2 864 6 7
cert_leafTestAt_block_2 864 7 8
cert_leafTestAt_block_2 864 8 9
cert_leafTestAt_block_2 864 9 10
cert_leafTestAt_block_2 864 10 11
cert_leafTestAt_block_2 864 11 12
cert_leafTestAt_block_2 864 12 13
cert_leafTestAt_block_2 864 13 14
cert_leafTestAt_block_2 864 14 15
cert_leafTestAt_block_2 864 15 16
cert_leafTestAt_block_2 864 16 17
cert_leafTestAt_block_2 864 17 18
cert_leafTestAt_block_2 864 18 19
cert_leafTestAt_block_2 864 19 20
cert_leafTestAt_block_2 864 20 21
cert_leafTestAt_block_2 864 21 22
cert_leafTestAt_block_2 864 22 23
cert_leafTestAt_block_2 864 23 24
cert_leafTestAt_block_2 864 24 25
cert_leafTestAt_block_2 864 25 26
cert_leafTestAt_block_2 864 26 27
cert_leafTestAt_block_2 864 27 28
cert_leafTestAt_block_2 864 28 29
cert_leafTestAt_block_2 864 29 30
cert_leafTestAt_block_2 864 30 31
cert_leafTestAt_block_2 864 31 32
theorem leafTestAt864_complete : Interval leafTestAt864 0 32 :=
  (interval_append leafTestAt864 0 16 32
  (interval_append leafTestAt864 0 8 16
  (interval_append leafTestAt864 0 4 8
  (interval_append leafTestAt864 0 2 4
  (interval_append leafTestAt864 0 1 2
  leafTestAt864_block_0
  leafTestAt864_block_1)
  (interval_append leafTestAt864 2 3 4
  leafTestAt864_block_2
  leafTestAt864_block_3))
  (interval_append leafTestAt864 4 6 8
  (interval_append leafTestAt864 4 5 6
  leafTestAt864_block_4
  leafTestAt864_block_5)
  (interval_append leafTestAt864 6 7 8
  leafTestAt864_block_6
  leafTestAt864_block_7)))
  (interval_append leafTestAt864 8 12 16
  (interval_append leafTestAt864 8 10 12
  (interval_append leafTestAt864 8 9 10
  leafTestAt864_block_8
  leafTestAt864_block_9)
  (interval_append leafTestAt864 10 11 12
  leafTestAt864_block_10
  leafTestAt864_block_11))
  (interval_append leafTestAt864 12 14 16
  (interval_append leafTestAt864 12 13 14
  leafTestAt864_block_12
  leafTestAt864_block_13)
  (interval_append leafTestAt864 14 15 16
  leafTestAt864_block_14
  leafTestAt864_block_15))))
  (interval_append leafTestAt864 16 24 32
  (interval_append leafTestAt864 16 20 24
  (interval_append leafTestAt864 16 18 20
  (interval_append leafTestAt864 16 17 18
  leafTestAt864_block_16
  leafTestAt864_block_17)
  (interval_append leafTestAt864 18 19 20
  leafTestAt864_block_18
  leafTestAt864_block_19))
  (interval_append leafTestAt864 20 22 24
  (interval_append leafTestAt864 20 21 22
  leafTestAt864_block_20
  leafTestAt864_block_21)
  (interval_append leafTestAt864 22 23 24
  leafTestAt864_block_22
  leafTestAt864_block_23)))
  (interval_append leafTestAt864 24 28 32
  (interval_append leafTestAt864 24 26 28
  (interval_append leafTestAt864 24 25 26
  leafTestAt864_block_24
  leafTestAt864_block_25)
  (interval_append leafTestAt864 26 27 28
  leafTestAt864_block_26
  leafTestAt864_block_27))
  (interval_append leafTestAt864 28 30 32
  (interval_append leafTestAt864 28 29 30
  leafTestAt864_block_28
  leafTestAt864_block_29)
  (interval_append leafTestAt864 30 31 32
  leafTestAt864_block_30
  leafTestAt864_block_31)))))
cert_leafInterval 864 896
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
