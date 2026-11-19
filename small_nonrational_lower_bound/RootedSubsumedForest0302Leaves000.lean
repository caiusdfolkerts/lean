module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0302Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 0
cert_leafTestAt_block_2 0 0 1
cert_leafTestAt_block_2 0 1 2
cert_leafTestAt_block_2 0 2 3
cert_leafTestAt_block_2 0 3 4
cert_leafTestAt_block_2 0 4 5
cert_leafTestAt_block_2 0 5 6
cert_leafTestAt_block_2 0 6 7
cert_leafTestAt_block_2 0 7 8
cert_leafTestAt_block_2 0 8 9
cert_leafTestAt_block_2 0 9 10
cert_leafTestAt_block_2 0 10 11
cert_leafTestAt_block_2 0 11 12
cert_leafTestAt_block_2 0 12 13
cert_leafTestAt_block_2 0 13 14
cert_leafTestAt_block_2 0 14 15
cert_leafTestAt_block_2 0 15 16
cert_leafTestAt_block_2 0 16 17
cert_leafTestAt_block_2 0 17 18
cert_leafTestAt_block_2 0 18 19
cert_leafTestAt_block_2 0 19 20
cert_leafTestAt_block_2 0 20 21
cert_leafTestAt_block_2 0 21 22
cert_leafTestAt_block_2 0 22 23
cert_leafTestAt_block_2 0 23 24
cert_leafTestAt_block_2 0 24 25
cert_leafTestAt_block_2 0 25 26
cert_leafTestAt_block_2 0 26 27
cert_leafTestAt_block_2 0 27 28
cert_leafTestAt_block_2 0 28 29
cert_leafTestAt_block_2 0 29 30
cert_leafTestAt_block_2 0 30 31
cert_leafTestAt_block_2 0 31 32
theorem leafTestAt0_complete : Interval leafTestAt0 0 32 :=
  (interval_append leafTestAt0 0 16 32
  (interval_append leafTestAt0 0 8 16
  (interval_append leafTestAt0 0 4 8
  (interval_append leafTestAt0 0 2 4
  (interval_append leafTestAt0 0 1 2
  leafTestAt0_block_0
  leafTestAt0_block_1)
  (interval_append leafTestAt0 2 3 4
  leafTestAt0_block_2
  leafTestAt0_block_3))
  (interval_append leafTestAt0 4 6 8
  (interval_append leafTestAt0 4 5 6
  leafTestAt0_block_4
  leafTestAt0_block_5)
  (interval_append leafTestAt0 6 7 8
  leafTestAt0_block_6
  leafTestAt0_block_7)))
  (interval_append leafTestAt0 8 12 16
  (interval_append leafTestAt0 8 10 12
  (interval_append leafTestAt0 8 9 10
  leafTestAt0_block_8
  leafTestAt0_block_9)
  (interval_append leafTestAt0 10 11 12
  leafTestAt0_block_10
  leafTestAt0_block_11))
  (interval_append leafTestAt0 12 14 16
  (interval_append leafTestAt0 12 13 14
  leafTestAt0_block_12
  leafTestAt0_block_13)
  (interval_append leafTestAt0 14 15 16
  leafTestAt0_block_14
  leafTestAt0_block_15))))
  (interval_append leafTestAt0 16 24 32
  (interval_append leafTestAt0 16 20 24
  (interval_append leafTestAt0 16 18 20
  (interval_append leafTestAt0 16 17 18
  leafTestAt0_block_16
  leafTestAt0_block_17)
  (interval_append leafTestAt0 18 19 20
  leafTestAt0_block_18
  leafTestAt0_block_19))
  (interval_append leafTestAt0 20 22 24
  (interval_append leafTestAt0 20 21 22
  leafTestAt0_block_20
  leafTestAt0_block_21)
  (interval_append leafTestAt0 22 23 24
  leafTestAt0_block_22
  leafTestAt0_block_23)))
  (interval_append leafTestAt0 24 28 32
  (interval_append leafTestAt0 24 26 28
  (interval_append leafTestAt0 24 25 26
  leafTestAt0_block_24
  leafTestAt0_block_25)
  (interval_append leafTestAt0 26 27 28
  leafTestAt0_block_26
  leafTestAt0_block_27))
  (interval_append leafTestAt0 28 30 32
  (interval_append leafTestAt0 28 29 30
  leafTestAt0_block_28
  leafTestAt0_block_29)
  (interval_append leafTestAt0 30 31 32
  leafTestAt0_block_30
  leafTestAt0_block_31)))))
cert_leafInterval 0 32
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
