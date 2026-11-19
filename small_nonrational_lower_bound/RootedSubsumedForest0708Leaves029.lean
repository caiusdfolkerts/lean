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
cert_leafTestAt 928
cert_leafTestAt_block_2 928 0 1
cert_leafTestAt_block_2 928 1 2
cert_leafTestAt_block_2 928 2 3
cert_leafTestAt_block_2 928 3 4
cert_leafTestAt_block_2 928 4 5
cert_leafTestAt_block_2 928 5 6
cert_leafTestAt_block_2 928 6 7
cert_leafTestAt_block_2 928 7 8
cert_leafTestAt_block_2 928 8 9
cert_leafTestAt_block_2 928 9 10
cert_leafTestAt_block_2 928 10 11
cert_leafTestAt_block_2 928 11 12
cert_leafTestAt_block_2 928 12 13
cert_leafTestAt_block_2 928 13 14
cert_leafTestAt_block_2 928 14 15
cert_leafTestAt_block_2 928 15 16
cert_leafTestAt_block_2 928 16 17
cert_leafTestAt_block_2 928 17 18
cert_leafTestAt_block_2 928 18 19
cert_leafTestAt_block_2 928 19 20
cert_leafTestAt_block_2 928 20 21
cert_leafTestAt_block_2 928 21 22
cert_leafTestAt_block_2 928 22 23
cert_leafTestAt_block_2 928 23 24
cert_leafTestAt_block_2 928 24 25
cert_leafTestAt_block_2 928 25 26
cert_leafTestAt_block_2 928 26 27
cert_leafTestAt_block_2 928 27 28
cert_leafTestAt_block_2 928 28 29
cert_leafTestAt_block_2 928 29 30
cert_leafTestAt_block_2 928 30 31
cert_leafTestAt_block_2 928 31 32
theorem leafTestAt928_complete : Interval leafTestAt928 0 32 :=
  (interval_append leafTestAt928 0 16 32
  (interval_append leafTestAt928 0 8 16
  (interval_append leafTestAt928 0 4 8
  (interval_append leafTestAt928 0 2 4
  (interval_append leafTestAt928 0 1 2
  leafTestAt928_block_0
  leafTestAt928_block_1)
  (interval_append leafTestAt928 2 3 4
  leafTestAt928_block_2
  leafTestAt928_block_3))
  (interval_append leafTestAt928 4 6 8
  (interval_append leafTestAt928 4 5 6
  leafTestAt928_block_4
  leafTestAt928_block_5)
  (interval_append leafTestAt928 6 7 8
  leafTestAt928_block_6
  leafTestAt928_block_7)))
  (interval_append leafTestAt928 8 12 16
  (interval_append leafTestAt928 8 10 12
  (interval_append leafTestAt928 8 9 10
  leafTestAt928_block_8
  leafTestAt928_block_9)
  (interval_append leafTestAt928 10 11 12
  leafTestAt928_block_10
  leafTestAt928_block_11))
  (interval_append leafTestAt928 12 14 16
  (interval_append leafTestAt928 12 13 14
  leafTestAt928_block_12
  leafTestAt928_block_13)
  (interval_append leafTestAt928 14 15 16
  leafTestAt928_block_14
  leafTestAt928_block_15))))
  (interval_append leafTestAt928 16 24 32
  (interval_append leafTestAt928 16 20 24
  (interval_append leafTestAt928 16 18 20
  (interval_append leafTestAt928 16 17 18
  leafTestAt928_block_16
  leafTestAt928_block_17)
  (interval_append leafTestAt928 18 19 20
  leafTestAt928_block_18
  leafTestAt928_block_19))
  (interval_append leafTestAt928 20 22 24
  (interval_append leafTestAt928 20 21 22
  leafTestAt928_block_20
  leafTestAt928_block_21)
  (interval_append leafTestAt928 22 23 24
  leafTestAt928_block_22
  leafTestAt928_block_23)))
  (interval_append leafTestAt928 24 28 32
  (interval_append leafTestAt928 24 26 28
  (interval_append leafTestAt928 24 25 26
  leafTestAt928_block_24
  leafTestAt928_block_25)
  (interval_append leafTestAt928 26 27 28
  leafTestAt928_block_26
  leafTestAt928_block_27))
  (interval_append leafTestAt928 28 30 32
  (interval_append leafTestAt928 28 29 30
  leafTestAt928_block_28
  leafTestAt928_block_29)
  (interval_append leafTestAt928 30 31 32
  leafTestAt928_block_30
  leafTestAt928_block_31)))))
cert_leafInterval 928 960
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
