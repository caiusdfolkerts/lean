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
theorem leafTestAt1600_complete : Interval leafTestAt1600 0 31 :=
  (interval_append leafTestAt1600 0 15 31
  (interval_append leafTestAt1600 0 7 15
  (interval_append leafTestAt1600 0 3 7
  (interval_append leafTestAt1600 0 1 3
  leafTestAt1600_block_0
  (interval_append leafTestAt1600 1 2 3
  leafTestAt1600_block_1
  leafTestAt1600_block_2))
  (interval_append leafTestAt1600 3 5 7
  (interval_append leafTestAt1600 3 4 5
  leafTestAt1600_block_3
  leafTestAt1600_block_4)
  (interval_append leafTestAt1600 5 6 7
  leafTestAt1600_block_5
  leafTestAt1600_block_6)))
  (interval_append leafTestAt1600 7 11 15
  (interval_append leafTestAt1600 7 9 11
  (interval_append leafTestAt1600 7 8 9
  leafTestAt1600_block_7
  leafTestAt1600_block_8)
  (interval_append leafTestAt1600 9 10 11
  leafTestAt1600_block_9
  leafTestAt1600_block_10))
  (interval_append leafTestAt1600 11 13 15
  (interval_append leafTestAt1600 11 12 13
  leafTestAt1600_block_11
  leafTestAt1600_block_12)
  (interval_append leafTestAt1600 13 14 15
  leafTestAt1600_block_13
  leafTestAt1600_block_14))))
  (interval_append leafTestAt1600 15 23 31
  (interval_append leafTestAt1600 15 19 23
  (interval_append leafTestAt1600 15 17 19
  (interval_append leafTestAt1600 15 16 17
  leafTestAt1600_block_15
  leafTestAt1600_block_16)
  (interval_append leafTestAt1600 17 18 19
  leafTestAt1600_block_17
  leafTestAt1600_block_18))
  (interval_append leafTestAt1600 19 21 23
  (interval_append leafTestAt1600 19 20 21
  leafTestAt1600_block_19
  leafTestAt1600_block_20)
  (interval_append leafTestAt1600 21 22 23
  leafTestAt1600_block_21
  leafTestAt1600_block_22)))
  (interval_append leafTestAt1600 23 27 31
  (interval_append leafTestAt1600 23 25 27
  (interval_append leafTestAt1600 23 24 25
  leafTestAt1600_block_23
  leafTestAt1600_block_24)
  (interval_append leafTestAt1600 25 26 27
  leafTestAt1600_block_25
  leafTestAt1600_block_26))
  (interval_append leafTestAt1600 27 29 31
  (interval_append leafTestAt1600 27 28 29
  leafTestAt1600_block_27
  leafTestAt1600_block_28)
  (interval_append leafTestAt1600 29 30 31
  leafTestAt1600_block_29
  leafTestAt1600_block_30)))))
cert_leafInterval 1600 1631
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
