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
cert_leafTestAt 832
cert_leafTestAt_block_2 832 0 1
cert_leafTestAt_block_2 832 1 2
cert_leafTestAt_block_2 832 2 3
cert_leafTestAt_block_2 832 3 4
cert_leafTestAt_block_2 832 4 5
cert_leafTestAt_block_2 832 5 6
cert_leafTestAt_block_2 832 6 7
cert_leafTestAt_block_2 832 7 8
cert_leafTestAt_block_2 832 8 9
cert_leafTestAt_block_2 832 9 10
cert_leafTestAt_block_2 832 10 11
cert_leafTestAt_block_2 832 11 12
cert_leafTestAt_block_2 832 12 13
cert_leafTestAt_block_2 832 13 14
cert_leafTestAt_block_2 832 14 15
cert_leafTestAt_block_2 832 15 16
cert_leafTestAt_block_2 832 16 17
cert_leafTestAt_block_2 832 17 18
cert_leafTestAt_block_2 832 18 19
cert_leafTestAt_block_2 832 19 20
cert_leafTestAt_block_2 832 20 21
cert_leafTestAt_block_2 832 21 22
cert_leafTestAt_block_2 832 22 23
cert_leafTestAt_block_2 832 23 24
cert_leafTestAt_block_2 832 24 25
cert_leafTestAt_block_2 832 25 26
cert_leafTestAt_block_2 832 26 27
cert_leafTestAt_block_2 832 27 28
cert_leafTestAt_block_2 832 28 29
cert_leafTestAt_block_2 832 29 30
cert_leafTestAt_block_2 832 30 31
cert_leafTestAt_block_2 832 31 32
theorem leafTestAt832_complete : Interval leafTestAt832 0 32 :=
  (interval_append leafTestAt832 0 16 32
  (interval_append leafTestAt832 0 8 16
  (interval_append leafTestAt832 0 4 8
  (interval_append leafTestAt832 0 2 4
  (interval_append leafTestAt832 0 1 2
  leafTestAt832_block_0
  leafTestAt832_block_1)
  (interval_append leafTestAt832 2 3 4
  leafTestAt832_block_2
  leafTestAt832_block_3))
  (interval_append leafTestAt832 4 6 8
  (interval_append leafTestAt832 4 5 6
  leafTestAt832_block_4
  leafTestAt832_block_5)
  (interval_append leafTestAt832 6 7 8
  leafTestAt832_block_6
  leafTestAt832_block_7)))
  (interval_append leafTestAt832 8 12 16
  (interval_append leafTestAt832 8 10 12
  (interval_append leafTestAt832 8 9 10
  leafTestAt832_block_8
  leafTestAt832_block_9)
  (interval_append leafTestAt832 10 11 12
  leafTestAt832_block_10
  leafTestAt832_block_11))
  (interval_append leafTestAt832 12 14 16
  (interval_append leafTestAt832 12 13 14
  leafTestAt832_block_12
  leafTestAt832_block_13)
  (interval_append leafTestAt832 14 15 16
  leafTestAt832_block_14
  leafTestAt832_block_15))))
  (interval_append leafTestAt832 16 24 32
  (interval_append leafTestAt832 16 20 24
  (interval_append leafTestAt832 16 18 20
  (interval_append leafTestAt832 16 17 18
  leafTestAt832_block_16
  leafTestAt832_block_17)
  (interval_append leafTestAt832 18 19 20
  leafTestAt832_block_18
  leafTestAt832_block_19))
  (interval_append leafTestAt832 20 22 24
  (interval_append leafTestAt832 20 21 22
  leafTestAt832_block_20
  leafTestAt832_block_21)
  (interval_append leafTestAt832 22 23 24
  leafTestAt832_block_22
  leafTestAt832_block_23)))
  (interval_append leafTestAt832 24 28 32
  (interval_append leafTestAt832 24 26 28
  (interval_append leafTestAt832 24 25 26
  leafTestAt832_block_24
  leafTestAt832_block_25)
  (interval_append leafTestAt832 26 27 28
  leafTestAt832_block_26
  leafTestAt832_block_27))
  (interval_append leafTestAt832 28 30 32
  (interval_append leafTestAt832 28 29 30
  leafTestAt832_block_28
  leafTestAt832_block_29)
  (interval_append leafTestAt832 30 31 32
  leafTestAt832_block_30
  leafTestAt832_block_31)))))
cert_leafInterval 832 864
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
