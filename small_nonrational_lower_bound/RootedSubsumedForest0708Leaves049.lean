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
cert_leafTestAt 1568
cert_leafTestAt_block_2 1568 0 1
cert_leafTestAt_block_2 1568 1 2
cert_leafTestAt_block_2 1568 2 3
cert_leafTestAt_block_2 1568 3 4
cert_leafTestAt_block_2 1568 4 5
cert_leafTestAt_block_2 1568 5 6
cert_leafTestAt_block_2 1568 6 7
cert_leafTestAt_block_2 1568 7 8
cert_leafTestAt_block_2 1568 8 9
cert_leafTestAt_block_2 1568 9 10
cert_leafTestAt_block_2 1568 10 11
cert_leafTestAt_block_2 1568 11 12
cert_leafTestAt_block_2 1568 12 13
cert_leafTestAt_block_2 1568 13 14
cert_leafTestAt_block_2 1568 14 15
cert_leafTestAt_block_2 1568 15 16
cert_leafTestAt_block_2 1568 16 17
cert_leafTestAt_block_2 1568 17 18
cert_leafTestAt_block_2 1568 18 19
cert_leafTestAt_block_2 1568 19 20
cert_leafTestAt_block_2 1568 20 21
cert_leafTestAt_block_2 1568 21 22
cert_leafTestAt_block_2 1568 22 23
cert_leafTestAt_block_2 1568 23 24
cert_leafTestAt_block_2 1568 24 25
cert_leafTestAt_block_2 1568 25 26
cert_leafTestAt_block_2 1568 26 27
cert_leafTestAt_block_2 1568 27 28
cert_leafTestAt_block_2 1568 28 29
cert_leafTestAt_block_2 1568 29 30
cert_leafTestAt_block_2 1568 30 31
cert_leafTestAt_block_2 1568 31 32
theorem leafTestAt1568_complete : Interval leafTestAt1568 0 32 :=
  (interval_append leafTestAt1568 0 16 32
  (interval_append leafTestAt1568 0 8 16
  (interval_append leafTestAt1568 0 4 8
  (interval_append leafTestAt1568 0 2 4
  (interval_append leafTestAt1568 0 1 2
  leafTestAt1568_block_0
  leafTestAt1568_block_1)
  (interval_append leafTestAt1568 2 3 4
  leafTestAt1568_block_2
  leafTestAt1568_block_3))
  (interval_append leafTestAt1568 4 6 8
  (interval_append leafTestAt1568 4 5 6
  leafTestAt1568_block_4
  leafTestAt1568_block_5)
  (interval_append leafTestAt1568 6 7 8
  leafTestAt1568_block_6
  leafTestAt1568_block_7)))
  (interval_append leafTestAt1568 8 12 16
  (interval_append leafTestAt1568 8 10 12
  (interval_append leafTestAt1568 8 9 10
  leafTestAt1568_block_8
  leafTestAt1568_block_9)
  (interval_append leafTestAt1568 10 11 12
  leafTestAt1568_block_10
  leafTestAt1568_block_11))
  (interval_append leafTestAt1568 12 14 16
  (interval_append leafTestAt1568 12 13 14
  leafTestAt1568_block_12
  leafTestAt1568_block_13)
  (interval_append leafTestAt1568 14 15 16
  leafTestAt1568_block_14
  leafTestAt1568_block_15))))
  (interval_append leafTestAt1568 16 24 32
  (interval_append leafTestAt1568 16 20 24
  (interval_append leafTestAt1568 16 18 20
  (interval_append leafTestAt1568 16 17 18
  leafTestAt1568_block_16
  leafTestAt1568_block_17)
  (interval_append leafTestAt1568 18 19 20
  leafTestAt1568_block_18
  leafTestAt1568_block_19))
  (interval_append leafTestAt1568 20 22 24
  (interval_append leafTestAt1568 20 21 22
  leafTestAt1568_block_20
  leafTestAt1568_block_21)
  (interval_append leafTestAt1568 22 23 24
  leafTestAt1568_block_22
  leafTestAt1568_block_23)))
  (interval_append leafTestAt1568 24 28 32
  (interval_append leafTestAt1568 24 26 28
  (interval_append leafTestAt1568 24 25 26
  leafTestAt1568_block_24
  leafTestAt1568_block_25)
  (interval_append leafTestAt1568 26 27 28
  leafTestAt1568_block_26
  leafTestAt1568_block_27))
  (interval_append leafTestAt1568 28 30 32
  (interval_append leafTestAt1568 28 29 30
  leafTestAt1568_block_28
  leafTestAt1568_block_29)
  (interval_append leafTestAt1568 30 31 32
  leafTestAt1568_block_30
  leafTestAt1568_block_31)))))
cert_leafInterval 1568 1600
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
