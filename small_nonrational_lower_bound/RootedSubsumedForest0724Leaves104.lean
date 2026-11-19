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
cert_leafTestAt 3328
cert_leafTestAt_block_2 3328 0 1
cert_leafTestAt_block_2 3328 1 2
cert_leafTestAt_block_2 3328 2 3
cert_leafTestAt_block_2 3328 3 4
cert_leafTestAt_block_2 3328 4 5
cert_leafTestAt_block_2 3328 5 6
cert_leafTestAt_block_2 3328 6 7
cert_leafTestAt_block_2 3328 7 8
cert_leafTestAt_block_2 3328 8 9
cert_leafTestAt_block_2 3328 9 10
cert_leafTestAt_block_2 3328 10 11
cert_leafTestAt_block_2 3328 11 12
cert_leafTestAt_block_2 3328 12 13
cert_leafTestAt_block_2 3328 13 14
cert_leafTestAt_block_2 3328 14 15
cert_leafTestAt_block_2 3328 15 16
cert_leafTestAt_block_2 3328 16 17
cert_leafTestAt_block_2 3328 17 18
cert_leafTestAt_block_2 3328 18 19
cert_leafTestAt_block_2 3328 19 20
cert_leafTestAt_block_2 3328 20 21
cert_leafTestAt_block_2 3328 21 22
cert_leafTestAt_block_2 3328 22 23
cert_leafTestAt_block_2 3328 23 24
cert_leafTestAt_block_2 3328 24 25
cert_leafTestAt_block_2 3328 25 26
cert_leafTestAt_block_2 3328 26 27
cert_leafTestAt_block_2 3328 27 28
cert_leafTestAt_block_2 3328 28 29
cert_leafTestAt_block_2 3328 29 30
cert_leafTestAt_block_2 3328 30 31
cert_leafTestAt_block_2 3328 31 32
theorem leafTestAt3328_complete : Interval leafTestAt3328 0 32 :=
  (interval_append leafTestAt3328 0 16 32
  (interval_append leafTestAt3328 0 8 16
  (interval_append leafTestAt3328 0 4 8
  (interval_append leafTestAt3328 0 2 4
  (interval_append leafTestAt3328 0 1 2
  leafTestAt3328_block_0
  leafTestAt3328_block_1)
  (interval_append leafTestAt3328 2 3 4
  leafTestAt3328_block_2
  leafTestAt3328_block_3))
  (interval_append leafTestAt3328 4 6 8
  (interval_append leafTestAt3328 4 5 6
  leafTestAt3328_block_4
  leafTestAt3328_block_5)
  (interval_append leafTestAt3328 6 7 8
  leafTestAt3328_block_6
  leafTestAt3328_block_7)))
  (interval_append leafTestAt3328 8 12 16
  (interval_append leafTestAt3328 8 10 12
  (interval_append leafTestAt3328 8 9 10
  leafTestAt3328_block_8
  leafTestAt3328_block_9)
  (interval_append leafTestAt3328 10 11 12
  leafTestAt3328_block_10
  leafTestAt3328_block_11))
  (interval_append leafTestAt3328 12 14 16
  (interval_append leafTestAt3328 12 13 14
  leafTestAt3328_block_12
  leafTestAt3328_block_13)
  (interval_append leafTestAt3328 14 15 16
  leafTestAt3328_block_14
  leafTestAt3328_block_15))))
  (interval_append leafTestAt3328 16 24 32
  (interval_append leafTestAt3328 16 20 24
  (interval_append leafTestAt3328 16 18 20
  (interval_append leafTestAt3328 16 17 18
  leafTestAt3328_block_16
  leafTestAt3328_block_17)
  (interval_append leafTestAt3328 18 19 20
  leafTestAt3328_block_18
  leafTestAt3328_block_19))
  (interval_append leafTestAt3328 20 22 24
  (interval_append leafTestAt3328 20 21 22
  leafTestAt3328_block_20
  leafTestAt3328_block_21)
  (interval_append leafTestAt3328 22 23 24
  leafTestAt3328_block_22
  leafTestAt3328_block_23)))
  (interval_append leafTestAt3328 24 28 32
  (interval_append leafTestAt3328 24 26 28
  (interval_append leafTestAt3328 24 25 26
  leafTestAt3328_block_24
  leafTestAt3328_block_25)
  (interval_append leafTestAt3328 26 27 28
  leafTestAt3328_block_26
  leafTestAt3328_block_27))
  (interval_append leafTestAt3328 28 30 32
  (interval_append leafTestAt3328 28 29 30
  leafTestAt3328_block_28
  leafTestAt3328_block_29)
  (interval_append leafTestAt3328 30 31 32
  leafTestAt3328_block_30
  leafTestAt3328_block_31)))))
cert_leafInterval 3328 3360
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
