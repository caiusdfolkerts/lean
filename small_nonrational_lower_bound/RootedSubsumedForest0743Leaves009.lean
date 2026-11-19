module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0743Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 288
cert_leafTestAt_block_2 288 0 1
cert_leafTestAt_block_2 288 1 2
cert_leafTestAt_block_2 288 2 3
cert_leafTestAt_block_2 288 3 4
cert_leafTestAt_block_2 288 4 5
cert_leafTestAt_block_2 288 5 6
cert_leafTestAt_block_2 288 6 7
cert_leafTestAt_block_2 288 7 8
cert_leafTestAt_block_2 288 8 9
cert_leafTestAt_block_2 288 9 10
cert_leafTestAt_block_2 288 10 11
cert_leafTestAt_block_2 288 11 12
cert_leafTestAt_block_2 288 12 13
cert_leafTestAt_block_2 288 13 14
cert_leafTestAt_block_2 288 14 15
cert_leafTestAt_block_2 288 15 16
cert_leafTestAt_block_2 288 16 17
cert_leafTestAt_block_2 288 17 18
cert_leafTestAt_block_2 288 18 19
cert_leafTestAt_block_2 288 19 20
cert_leafTestAt_block_2 288 20 21
cert_leafTestAt_block_2 288 21 22
cert_leafTestAt_block_2 288 22 23
cert_leafTestAt_block_2 288 23 24
cert_leafTestAt_block_2 288 24 25
cert_leafTestAt_block_2 288 25 26
cert_leafTestAt_block_2 288 26 27
cert_leafTestAt_block_2 288 27 28
cert_leafTestAt_block_2 288 28 29
cert_leafTestAt_block_2 288 29 30
cert_leafTestAt_block_2 288 30 31
cert_leafTestAt_block_2 288 31 32
theorem leafTestAt288_complete : Interval leafTestAt288 0 32 :=
  (interval_append leafTestAt288 0 16 32
  (interval_append leafTestAt288 0 8 16
  (interval_append leafTestAt288 0 4 8
  (interval_append leafTestAt288 0 2 4
  (interval_append leafTestAt288 0 1 2
  leafTestAt288_block_0
  leafTestAt288_block_1)
  (interval_append leafTestAt288 2 3 4
  leafTestAt288_block_2
  leafTestAt288_block_3))
  (interval_append leafTestAt288 4 6 8
  (interval_append leafTestAt288 4 5 6
  leafTestAt288_block_4
  leafTestAt288_block_5)
  (interval_append leafTestAt288 6 7 8
  leafTestAt288_block_6
  leafTestAt288_block_7)))
  (interval_append leafTestAt288 8 12 16
  (interval_append leafTestAt288 8 10 12
  (interval_append leafTestAt288 8 9 10
  leafTestAt288_block_8
  leafTestAt288_block_9)
  (interval_append leafTestAt288 10 11 12
  leafTestAt288_block_10
  leafTestAt288_block_11))
  (interval_append leafTestAt288 12 14 16
  (interval_append leafTestAt288 12 13 14
  leafTestAt288_block_12
  leafTestAt288_block_13)
  (interval_append leafTestAt288 14 15 16
  leafTestAt288_block_14
  leafTestAt288_block_15))))
  (interval_append leafTestAt288 16 24 32
  (interval_append leafTestAt288 16 20 24
  (interval_append leafTestAt288 16 18 20
  (interval_append leafTestAt288 16 17 18
  leafTestAt288_block_16
  leafTestAt288_block_17)
  (interval_append leafTestAt288 18 19 20
  leafTestAt288_block_18
  leafTestAt288_block_19))
  (interval_append leafTestAt288 20 22 24
  (interval_append leafTestAt288 20 21 22
  leafTestAt288_block_20
  leafTestAt288_block_21)
  (interval_append leafTestAt288 22 23 24
  leafTestAt288_block_22
  leafTestAt288_block_23)))
  (interval_append leafTestAt288 24 28 32
  (interval_append leafTestAt288 24 26 28
  (interval_append leafTestAt288 24 25 26
  leafTestAt288_block_24
  leafTestAt288_block_25)
  (interval_append leafTestAt288 26 27 28
  leafTestAt288_block_26
  leafTestAt288_block_27))
  (interval_append leafTestAt288 28 30 32
  (interval_append leafTestAt288 28 29 30
  leafTestAt288_block_28
  leafTestAt288_block_29)
  (interval_append leafTestAt288 30 31 32
  leafTestAt288_block_30
  leafTestAt288_block_31)))))
cert_leafInterval 288 320
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
