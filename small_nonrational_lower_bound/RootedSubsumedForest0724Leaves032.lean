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
cert_leafTestAt 1024
cert_leafTestAt_block_2 1024 0 1
cert_leafTestAt_block_2 1024 1 2
cert_leafTestAt_block_2 1024 2 3
cert_leafTestAt_block_2 1024 3 4
cert_leafTestAt_block_2 1024 4 5
cert_leafTestAt_block_2 1024 5 6
cert_leafTestAt_block_2 1024 6 7
cert_leafTestAt_block_2 1024 7 8
cert_leafTestAt_block_2 1024 8 9
cert_leafTestAt_block_2 1024 9 10
cert_leafTestAt_block_2 1024 10 11
cert_leafTestAt_block_2 1024 11 12
cert_leafTestAt_block_2 1024 12 13
cert_leafTestAt_block_2 1024 13 14
cert_leafTestAt_block_2 1024 14 15
cert_leafTestAt_block_2 1024 15 16
cert_leafTestAt_block_2 1024 16 17
cert_leafTestAt_block_2 1024 17 18
cert_leafTestAt_block_2 1024 18 19
cert_leafTestAt_block_2 1024 19 20
cert_leafTestAt_block_2 1024 20 21
cert_leafTestAt_block_2 1024 21 22
cert_leafTestAt_block_2 1024 22 23
cert_leafTestAt_block_2 1024 23 24
cert_leafTestAt_block_2 1024 24 25
cert_leafTestAt_block_2 1024 25 26
cert_leafTestAt_block_2 1024 26 27
cert_leafTestAt_block_2 1024 27 28
cert_leafTestAt_block_2 1024 28 29
cert_leafTestAt_block_2 1024 29 30
cert_leafTestAt_block_2 1024 30 31
cert_leafTestAt_block_2 1024 31 32
theorem leafTestAt1024_complete : Interval leafTestAt1024 0 32 :=
  (interval_append leafTestAt1024 0 16 32
  (interval_append leafTestAt1024 0 8 16
  (interval_append leafTestAt1024 0 4 8
  (interval_append leafTestAt1024 0 2 4
  (interval_append leafTestAt1024 0 1 2
  leafTestAt1024_block_0
  leafTestAt1024_block_1)
  (interval_append leafTestAt1024 2 3 4
  leafTestAt1024_block_2
  leafTestAt1024_block_3))
  (interval_append leafTestAt1024 4 6 8
  (interval_append leafTestAt1024 4 5 6
  leafTestAt1024_block_4
  leafTestAt1024_block_5)
  (interval_append leafTestAt1024 6 7 8
  leafTestAt1024_block_6
  leafTestAt1024_block_7)))
  (interval_append leafTestAt1024 8 12 16
  (interval_append leafTestAt1024 8 10 12
  (interval_append leafTestAt1024 8 9 10
  leafTestAt1024_block_8
  leafTestAt1024_block_9)
  (interval_append leafTestAt1024 10 11 12
  leafTestAt1024_block_10
  leafTestAt1024_block_11))
  (interval_append leafTestAt1024 12 14 16
  (interval_append leafTestAt1024 12 13 14
  leafTestAt1024_block_12
  leafTestAt1024_block_13)
  (interval_append leafTestAt1024 14 15 16
  leafTestAt1024_block_14
  leafTestAt1024_block_15))))
  (interval_append leafTestAt1024 16 24 32
  (interval_append leafTestAt1024 16 20 24
  (interval_append leafTestAt1024 16 18 20
  (interval_append leafTestAt1024 16 17 18
  leafTestAt1024_block_16
  leafTestAt1024_block_17)
  (interval_append leafTestAt1024 18 19 20
  leafTestAt1024_block_18
  leafTestAt1024_block_19))
  (interval_append leafTestAt1024 20 22 24
  (interval_append leafTestAt1024 20 21 22
  leafTestAt1024_block_20
  leafTestAt1024_block_21)
  (interval_append leafTestAt1024 22 23 24
  leafTestAt1024_block_22
  leafTestAt1024_block_23)))
  (interval_append leafTestAt1024 24 28 32
  (interval_append leafTestAt1024 24 26 28
  (interval_append leafTestAt1024 24 25 26
  leafTestAt1024_block_24
  leafTestAt1024_block_25)
  (interval_append leafTestAt1024 26 27 28
  leafTestAt1024_block_26
  leafTestAt1024_block_27))
  (interval_append leafTestAt1024 28 30 32
  (interval_append leafTestAt1024 28 29 30
  leafTestAt1024_block_28
  leafTestAt1024_block_29)
  (interval_append leafTestAt1024 30 31 32
  leafTestAt1024_block_30
  leafTestAt1024_block_31)))))
cert_leafInterval 1024 1056
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
