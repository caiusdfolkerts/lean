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
cert_leafTestAt 736
cert_leafTestAt_block_2 736 0 1
cert_leafTestAt_block_2 736 1 2
cert_leafTestAt_block_2 736 2 3
cert_leafTestAt_block_2 736 3 4
cert_leafTestAt_block_2 736 4 5
cert_leafTestAt_block_2 736 5 6
cert_leafTestAt_block_2 736 6 7
cert_leafTestAt_block_2 736 7 8
cert_leafTestAt_block_2 736 8 9
cert_leafTestAt_block_2 736 9 10
cert_leafTestAt_block_2 736 10 11
cert_leafTestAt_block_2 736 11 12
cert_leafTestAt_block_2 736 12 13
cert_leafTestAt_block_2 736 13 14
cert_leafTestAt_block_2 736 14 15
cert_leafTestAt_block_2 736 15 16
cert_leafTestAt_block_2 736 16 17
cert_leafTestAt_block_2 736 17 18
cert_leafTestAt_block_2 736 18 19
cert_leafTestAt_block_2 736 19 20
cert_leafTestAt_block_2 736 20 21
cert_leafTestAt_block_2 736 21 22
cert_leafTestAt_block_2 736 22 23
cert_leafTestAt_block_2 736 23 24
cert_leafTestAt_block_2 736 24 25
cert_leafTestAt_block_2 736 25 26
cert_leafTestAt_block_2 736 26 27
cert_leafTestAt_block_2 736 27 28
cert_leafTestAt_block_2 736 28 29
cert_leafTestAt_block_2 736 29 30
cert_leafTestAt_block_2 736 30 31
cert_leafTestAt_block_2 736 31 32
theorem leafTestAt736_complete : Interval leafTestAt736 0 32 :=
  (interval_append leafTestAt736 0 16 32
  (interval_append leafTestAt736 0 8 16
  (interval_append leafTestAt736 0 4 8
  (interval_append leafTestAt736 0 2 4
  (interval_append leafTestAt736 0 1 2
  leafTestAt736_block_0
  leafTestAt736_block_1)
  (interval_append leafTestAt736 2 3 4
  leafTestAt736_block_2
  leafTestAt736_block_3))
  (interval_append leafTestAt736 4 6 8
  (interval_append leafTestAt736 4 5 6
  leafTestAt736_block_4
  leafTestAt736_block_5)
  (interval_append leafTestAt736 6 7 8
  leafTestAt736_block_6
  leafTestAt736_block_7)))
  (interval_append leafTestAt736 8 12 16
  (interval_append leafTestAt736 8 10 12
  (interval_append leafTestAt736 8 9 10
  leafTestAt736_block_8
  leafTestAt736_block_9)
  (interval_append leafTestAt736 10 11 12
  leafTestAt736_block_10
  leafTestAt736_block_11))
  (interval_append leafTestAt736 12 14 16
  (interval_append leafTestAt736 12 13 14
  leafTestAt736_block_12
  leafTestAt736_block_13)
  (interval_append leafTestAt736 14 15 16
  leafTestAt736_block_14
  leafTestAt736_block_15))))
  (interval_append leafTestAt736 16 24 32
  (interval_append leafTestAt736 16 20 24
  (interval_append leafTestAt736 16 18 20
  (interval_append leafTestAt736 16 17 18
  leafTestAt736_block_16
  leafTestAt736_block_17)
  (interval_append leafTestAt736 18 19 20
  leafTestAt736_block_18
  leafTestAt736_block_19))
  (interval_append leafTestAt736 20 22 24
  (interval_append leafTestAt736 20 21 22
  leafTestAt736_block_20
  leafTestAt736_block_21)
  (interval_append leafTestAt736 22 23 24
  leafTestAt736_block_22
  leafTestAt736_block_23)))
  (interval_append leafTestAt736 24 28 32
  (interval_append leafTestAt736 24 26 28
  (interval_append leafTestAt736 24 25 26
  leafTestAt736_block_24
  leafTestAt736_block_25)
  (interval_append leafTestAt736 26 27 28
  leafTestAt736_block_26
  leafTestAt736_block_27))
  (interval_append leafTestAt736 28 30 32
  (interval_append leafTestAt736 28 29 30
  leafTestAt736_block_28
  leafTestAt736_block_29)
  (interval_append leafTestAt736 30 31 32
  leafTestAt736_block_30
  leafTestAt736_block_31)))))
cert_leafInterval 736 768
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
