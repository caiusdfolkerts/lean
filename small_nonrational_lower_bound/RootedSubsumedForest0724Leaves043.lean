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
cert_leafTestAt 1376
cert_leafTestAt_block_2 1376 0 1
cert_leafTestAt_block_2 1376 1 2
cert_leafTestAt_block_2 1376 2 3
cert_leafTestAt_block_2 1376 3 4
cert_leafTestAt_block_2 1376 4 5
cert_leafTestAt_block_2 1376 5 6
cert_leafTestAt_block_2 1376 6 7
cert_leafTestAt_block_2 1376 7 8
cert_leafTestAt_block_2 1376 8 9
cert_leafTestAt_block_2 1376 9 10
cert_leafTestAt_block_2 1376 10 11
cert_leafTestAt_block_2 1376 11 12
cert_leafTestAt_block_2 1376 12 13
cert_leafTestAt_block_2 1376 13 14
cert_leafTestAt_block_2 1376 14 15
cert_leafTestAt_block_2 1376 15 16
cert_leafTestAt_block_2 1376 16 17
cert_leafTestAt_block_2 1376 17 18
cert_leafTestAt_block_2 1376 18 19
cert_leafTestAt_block_2 1376 19 20
cert_leafTestAt_block_2 1376 20 21
cert_leafTestAt_block_2 1376 21 22
cert_leafTestAt_block_2 1376 22 23
cert_leafTestAt_block_2 1376 23 24
cert_leafTestAt_block_2 1376 24 25
cert_leafTestAt_block_2 1376 25 26
cert_leafTestAt_block_2 1376 26 27
cert_leafTestAt_block_2 1376 27 28
cert_leafTestAt_block_2 1376 28 29
cert_leafTestAt_block_2 1376 29 30
cert_leafTestAt_block_2 1376 30 31
cert_leafTestAt_block_2 1376 31 32
theorem leafTestAt1376_complete : Interval leafTestAt1376 0 32 :=
  (interval_append leafTestAt1376 0 16 32
  (interval_append leafTestAt1376 0 8 16
  (interval_append leafTestAt1376 0 4 8
  (interval_append leafTestAt1376 0 2 4
  (interval_append leafTestAt1376 0 1 2
  leafTestAt1376_block_0
  leafTestAt1376_block_1)
  (interval_append leafTestAt1376 2 3 4
  leafTestAt1376_block_2
  leafTestAt1376_block_3))
  (interval_append leafTestAt1376 4 6 8
  (interval_append leafTestAt1376 4 5 6
  leafTestAt1376_block_4
  leafTestAt1376_block_5)
  (interval_append leafTestAt1376 6 7 8
  leafTestAt1376_block_6
  leafTestAt1376_block_7)))
  (interval_append leafTestAt1376 8 12 16
  (interval_append leafTestAt1376 8 10 12
  (interval_append leafTestAt1376 8 9 10
  leafTestAt1376_block_8
  leafTestAt1376_block_9)
  (interval_append leafTestAt1376 10 11 12
  leafTestAt1376_block_10
  leafTestAt1376_block_11))
  (interval_append leafTestAt1376 12 14 16
  (interval_append leafTestAt1376 12 13 14
  leafTestAt1376_block_12
  leafTestAt1376_block_13)
  (interval_append leafTestAt1376 14 15 16
  leafTestAt1376_block_14
  leafTestAt1376_block_15))))
  (interval_append leafTestAt1376 16 24 32
  (interval_append leafTestAt1376 16 20 24
  (interval_append leafTestAt1376 16 18 20
  (interval_append leafTestAt1376 16 17 18
  leafTestAt1376_block_16
  leafTestAt1376_block_17)
  (interval_append leafTestAt1376 18 19 20
  leafTestAt1376_block_18
  leafTestAt1376_block_19))
  (interval_append leafTestAt1376 20 22 24
  (interval_append leafTestAt1376 20 21 22
  leafTestAt1376_block_20
  leafTestAt1376_block_21)
  (interval_append leafTestAt1376 22 23 24
  leafTestAt1376_block_22
  leafTestAt1376_block_23)))
  (interval_append leafTestAt1376 24 28 32
  (interval_append leafTestAt1376 24 26 28
  (interval_append leafTestAt1376 24 25 26
  leafTestAt1376_block_24
  leafTestAt1376_block_25)
  (interval_append leafTestAt1376 26 27 28
  leafTestAt1376_block_26
  leafTestAt1376_block_27))
  (interval_append leafTestAt1376 28 30 32
  (interval_append leafTestAt1376 28 29 30
  leafTestAt1376_block_28
  leafTestAt1376_block_29)
  (interval_append leafTestAt1376 30 31 32
  leafTestAt1376_block_30
  leafTestAt1376_block_31)))))
cert_leafInterval 1376 1408
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
