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
cert_leafTestAt 3040
cert_leafTestAt_block_2 3040 0 1
cert_leafTestAt_block_2 3040 1 2
cert_leafTestAt_block_2 3040 2 3
cert_leafTestAt_block_2 3040 3 4
cert_leafTestAt_block_2 3040 4 5
cert_leafTestAt_block_2 3040 5 6
cert_leafTestAt_block_2 3040 6 7
cert_leafTestAt_block_2 3040 7 8
cert_leafTestAt_block_2 3040 8 9
cert_leafTestAt_block_2 3040 9 10
cert_leafTestAt_block_2 3040 10 11
cert_leafTestAt_block_2 3040 11 12
cert_leafTestAt_block_2 3040 12 13
cert_leafTestAt_block_2 3040 13 14
cert_leafTestAt_block_2 3040 14 15
cert_leafTestAt_block_2 3040 15 16
cert_leafTestAt_block_2 3040 16 17
cert_leafTestAt_block_2 3040 17 18
cert_leafTestAt_block_2 3040 18 19
cert_leafTestAt_block_2 3040 19 20
cert_leafTestAt_block_2 3040 20 21
cert_leafTestAt_block_2 3040 21 22
cert_leafTestAt_block_2 3040 22 23
cert_leafTestAt_block_2 3040 23 24
cert_leafTestAt_block_2 3040 24 25
cert_leafTestAt_block_2 3040 25 26
cert_leafTestAt_block_2 3040 26 27
cert_leafTestAt_block_2 3040 27 28
cert_leafTestAt_block_2 3040 28 29
cert_leafTestAt_block_2 3040 29 30
cert_leafTestAt_block_2 3040 30 31
cert_leafTestAt_block_2 3040 31 32
theorem leafTestAt3040_complete : Interval leafTestAt3040 0 32 :=
  (interval_append leafTestAt3040 0 16 32
  (interval_append leafTestAt3040 0 8 16
  (interval_append leafTestAt3040 0 4 8
  (interval_append leafTestAt3040 0 2 4
  (interval_append leafTestAt3040 0 1 2
  leafTestAt3040_block_0
  leafTestAt3040_block_1)
  (interval_append leafTestAt3040 2 3 4
  leafTestAt3040_block_2
  leafTestAt3040_block_3))
  (interval_append leafTestAt3040 4 6 8
  (interval_append leafTestAt3040 4 5 6
  leafTestAt3040_block_4
  leafTestAt3040_block_5)
  (interval_append leafTestAt3040 6 7 8
  leafTestAt3040_block_6
  leafTestAt3040_block_7)))
  (interval_append leafTestAt3040 8 12 16
  (interval_append leafTestAt3040 8 10 12
  (interval_append leafTestAt3040 8 9 10
  leafTestAt3040_block_8
  leafTestAt3040_block_9)
  (interval_append leafTestAt3040 10 11 12
  leafTestAt3040_block_10
  leafTestAt3040_block_11))
  (interval_append leafTestAt3040 12 14 16
  (interval_append leafTestAt3040 12 13 14
  leafTestAt3040_block_12
  leafTestAt3040_block_13)
  (interval_append leafTestAt3040 14 15 16
  leafTestAt3040_block_14
  leafTestAt3040_block_15))))
  (interval_append leafTestAt3040 16 24 32
  (interval_append leafTestAt3040 16 20 24
  (interval_append leafTestAt3040 16 18 20
  (interval_append leafTestAt3040 16 17 18
  leafTestAt3040_block_16
  leafTestAt3040_block_17)
  (interval_append leafTestAt3040 18 19 20
  leafTestAt3040_block_18
  leafTestAt3040_block_19))
  (interval_append leafTestAt3040 20 22 24
  (interval_append leafTestAt3040 20 21 22
  leafTestAt3040_block_20
  leafTestAt3040_block_21)
  (interval_append leafTestAt3040 22 23 24
  leafTestAt3040_block_22
  leafTestAt3040_block_23)))
  (interval_append leafTestAt3040 24 28 32
  (interval_append leafTestAt3040 24 26 28
  (interval_append leafTestAt3040 24 25 26
  leafTestAt3040_block_24
  leafTestAt3040_block_25)
  (interval_append leafTestAt3040 26 27 28
  leafTestAt3040_block_26
  leafTestAt3040_block_27))
  (interval_append leafTestAt3040 28 30 32
  (interval_append leafTestAt3040 28 29 30
  leafTestAt3040_block_28
  leafTestAt3040_block_29)
  (interval_append leafTestAt3040 30 31 32
  leafTestAt3040_block_30
  leafTestAt3040_block_31)))))
cert_leafInterval 3040 3072
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
