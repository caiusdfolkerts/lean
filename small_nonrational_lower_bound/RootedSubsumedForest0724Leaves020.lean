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
cert_leafTestAt 640
cert_leafTestAt_block_2 640 0 1
cert_leafTestAt_block_2 640 1 2
cert_leafTestAt_block_2 640 2 3
cert_leafTestAt_block_2 640 3 4
cert_leafTestAt_block_2 640 4 5
cert_leafTestAt_block_2 640 5 6
cert_leafTestAt_block_2 640 6 7
cert_leafTestAt_block_2 640 7 8
cert_leafTestAt_block_2 640 8 9
cert_leafTestAt_block_2 640 9 10
cert_leafTestAt_block_2 640 10 11
cert_leafTestAt_block_2 640 11 12
cert_leafTestAt_block_2 640 12 13
cert_leafTestAt_block_2 640 13 14
cert_leafTestAt_block_2 640 14 15
cert_leafTestAt_block_2 640 15 16
cert_leafTestAt_block_2 640 16 17
cert_leafTestAt_block_2 640 17 18
cert_leafTestAt_block_2 640 18 19
cert_leafTestAt_block_2 640 19 20
cert_leafTestAt_block_2 640 20 21
cert_leafTestAt_block_2 640 21 22
cert_leafTestAt_block_2 640 22 23
cert_leafTestAt_block_2 640 23 24
cert_leafTestAt_block_2 640 24 25
cert_leafTestAt_block_2 640 25 26
cert_leafTestAt_block_2 640 26 27
cert_leafTestAt_block_2 640 27 28
cert_leafTestAt_block_2 640 28 29
cert_leafTestAt_block_2 640 29 30
cert_leafTestAt_block_2 640 30 31
cert_leafTestAt_block_2 640 31 32
theorem leafTestAt640_complete : Interval leafTestAt640 0 32 :=
  (interval_append leafTestAt640 0 16 32
  (interval_append leafTestAt640 0 8 16
  (interval_append leafTestAt640 0 4 8
  (interval_append leafTestAt640 0 2 4
  (interval_append leafTestAt640 0 1 2
  leafTestAt640_block_0
  leafTestAt640_block_1)
  (interval_append leafTestAt640 2 3 4
  leafTestAt640_block_2
  leafTestAt640_block_3))
  (interval_append leafTestAt640 4 6 8
  (interval_append leafTestAt640 4 5 6
  leafTestAt640_block_4
  leafTestAt640_block_5)
  (interval_append leafTestAt640 6 7 8
  leafTestAt640_block_6
  leafTestAt640_block_7)))
  (interval_append leafTestAt640 8 12 16
  (interval_append leafTestAt640 8 10 12
  (interval_append leafTestAt640 8 9 10
  leafTestAt640_block_8
  leafTestAt640_block_9)
  (interval_append leafTestAt640 10 11 12
  leafTestAt640_block_10
  leafTestAt640_block_11))
  (interval_append leafTestAt640 12 14 16
  (interval_append leafTestAt640 12 13 14
  leafTestAt640_block_12
  leafTestAt640_block_13)
  (interval_append leafTestAt640 14 15 16
  leafTestAt640_block_14
  leafTestAt640_block_15))))
  (interval_append leafTestAt640 16 24 32
  (interval_append leafTestAt640 16 20 24
  (interval_append leafTestAt640 16 18 20
  (interval_append leafTestAt640 16 17 18
  leafTestAt640_block_16
  leafTestAt640_block_17)
  (interval_append leafTestAt640 18 19 20
  leafTestAt640_block_18
  leafTestAt640_block_19))
  (interval_append leafTestAt640 20 22 24
  (interval_append leafTestAt640 20 21 22
  leafTestAt640_block_20
  leafTestAt640_block_21)
  (interval_append leafTestAt640 22 23 24
  leafTestAt640_block_22
  leafTestAt640_block_23)))
  (interval_append leafTestAt640 24 28 32
  (interval_append leafTestAt640 24 26 28
  (interval_append leafTestAt640 24 25 26
  leafTestAt640_block_24
  leafTestAt640_block_25)
  (interval_append leafTestAt640 26 27 28
  leafTestAt640_block_26
  leafTestAt640_block_27))
  (interval_append leafTestAt640 28 30 32
  (interval_append leafTestAt640 28 29 30
  leafTestAt640_block_28
  leafTestAt640_block_29)
  (interval_append leafTestAt640 30 31 32
  leafTestAt640_block_30
  leafTestAt640_block_31)))))
cert_leafInterval 640 672
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
