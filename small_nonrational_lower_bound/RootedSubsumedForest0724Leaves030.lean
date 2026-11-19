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
cert_leafTestAt 960
cert_leafTestAt_block_2 960 0 1
cert_leafTestAt_block_2 960 1 2
cert_leafTestAt_block_2 960 2 3
cert_leafTestAt_block_2 960 3 4
cert_leafTestAt_block_2 960 4 5
cert_leafTestAt_block_2 960 5 6
cert_leafTestAt_block_2 960 6 7
cert_leafTestAt_block_2 960 7 8
cert_leafTestAt_block_2 960 8 9
cert_leafTestAt_block_2 960 9 10
cert_leafTestAt_block_2 960 10 11
cert_leafTestAt_block_2 960 11 12
cert_leafTestAt_block_2 960 12 13
cert_leafTestAt_block_2 960 13 14
cert_leafTestAt_block_2 960 14 15
cert_leafTestAt_block_2 960 15 16
cert_leafTestAt_block_2 960 16 17
cert_leafTestAt_block_2 960 17 18
cert_leafTestAt_block_2 960 18 19
cert_leafTestAt_block_2 960 19 20
cert_leafTestAt_block_2 960 20 21
cert_leafTestAt_block_2 960 21 22
cert_leafTestAt_block_2 960 22 23
cert_leafTestAt_block_2 960 23 24
cert_leafTestAt_block_2 960 24 25
cert_leafTestAt_block_2 960 25 26
cert_leafTestAt_block_2 960 26 27
cert_leafTestAt_block_2 960 27 28
cert_leafTestAt_block_2 960 28 29
cert_leafTestAt_block_2 960 29 30
cert_leafTestAt_block_2 960 30 31
cert_leafTestAt_block_2 960 31 32
theorem leafTestAt960_complete : Interval leafTestAt960 0 32 :=
  (interval_append leafTestAt960 0 16 32
  (interval_append leafTestAt960 0 8 16
  (interval_append leafTestAt960 0 4 8
  (interval_append leafTestAt960 0 2 4
  (interval_append leafTestAt960 0 1 2
  leafTestAt960_block_0
  leafTestAt960_block_1)
  (interval_append leafTestAt960 2 3 4
  leafTestAt960_block_2
  leafTestAt960_block_3))
  (interval_append leafTestAt960 4 6 8
  (interval_append leafTestAt960 4 5 6
  leafTestAt960_block_4
  leafTestAt960_block_5)
  (interval_append leafTestAt960 6 7 8
  leafTestAt960_block_6
  leafTestAt960_block_7)))
  (interval_append leafTestAt960 8 12 16
  (interval_append leafTestAt960 8 10 12
  (interval_append leafTestAt960 8 9 10
  leafTestAt960_block_8
  leafTestAt960_block_9)
  (interval_append leafTestAt960 10 11 12
  leafTestAt960_block_10
  leafTestAt960_block_11))
  (interval_append leafTestAt960 12 14 16
  (interval_append leafTestAt960 12 13 14
  leafTestAt960_block_12
  leafTestAt960_block_13)
  (interval_append leafTestAt960 14 15 16
  leafTestAt960_block_14
  leafTestAt960_block_15))))
  (interval_append leafTestAt960 16 24 32
  (interval_append leafTestAt960 16 20 24
  (interval_append leafTestAt960 16 18 20
  (interval_append leafTestAt960 16 17 18
  leafTestAt960_block_16
  leafTestAt960_block_17)
  (interval_append leafTestAt960 18 19 20
  leafTestAt960_block_18
  leafTestAt960_block_19))
  (interval_append leafTestAt960 20 22 24
  (interval_append leafTestAt960 20 21 22
  leafTestAt960_block_20
  leafTestAt960_block_21)
  (interval_append leafTestAt960 22 23 24
  leafTestAt960_block_22
  leafTestAt960_block_23)))
  (interval_append leafTestAt960 24 28 32
  (interval_append leafTestAt960 24 26 28
  (interval_append leafTestAt960 24 25 26
  leafTestAt960_block_24
  leafTestAt960_block_25)
  (interval_append leafTestAt960 26 27 28
  leafTestAt960_block_26
  leafTestAt960_block_27))
  (interval_append leafTestAt960 28 30 32
  (interval_append leafTestAt960 28 29 30
  leafTestAt960_block_28
  leafTestAt960_block_29)
  (interval_append leafTestAt960 30 31 32
  leafTestAt960_block_30
  leafTestAt960_block_31)))))
cert_leafInterval 960 992
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
