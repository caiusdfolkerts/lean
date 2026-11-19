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
cert_leafTestAt 512
cert_leafTestAt_block_2 512 0 1
cert_leafTestAt_block_2 512 1 2
cert_leafTestAt_block_2 512 2 3
cert_leafTestAt_block_2 512 3 4
cert_leafTestAt_block_2 512 4 5
cert_leafTestAt_block_2 512 5 6
cert_leafTestAt_block_2 512 6 7
cert_leafTestAt_block_2 512 7 8
cert_leafTestAt_block_2 512 8 9
cert_leafTestAt_block_2 512 9 10
cert_leafTestAt_block_2 512 10 11
cert_leafTestAt_block_2 512 11 12
cert_leafTestAt_block_2 512 12 13
cert_leafTestAt_block_2 512 13 14
cert_leafTestAt_block_2 512 14 15
cert_leafTestAt_block_2 512 15 16
cert_leafTestAt_block_2 512 16 17
cert_leafTestAt_block_2 512 17 18
cert_leafTestAt_block_2 512 18 19
cert_leafTestAt_block_2 512 19 20
cert_leafTestAt_block_2 512 20 21
cert_leafTestAt_block_2 512 21 22
cert_leafTestAt_block_2 512 22 23
cert_leafTestAt_block_2 512 23 24
cert_leafTestAt_block_2 512 24 25
cert_leafTestAt_block_2 512 25 26
cert_leafTestAt_block_2 512 26 27
cert_leafTestAt_block_2 512 27 28
cert_leafTestAt_block_2 512 28 29
cert_leafTestAt_block_2 512 29 30
cert_leafTestAt_block_2 512 30 31
cert_leafTestAt_block_2 512 31 32
theorem leafTestAt512_complete : Interval leafTestAt512 0 32 :=
  (interval_append leafTestAt512 0 16 32
  (interval_append leafTestAt512 0 8 16
  (interval_append leafTestAt512 0 4 8
  (interval_append leafTestAt512 0 2 4
  (interval_append leafTestAt512 0 1 2
  leafTestAt512_block_0
  leafTestAt512_block_1)
  (interval_append leafTestAt512 2 3 4
  leafTestAt512_block_2
  leafTestAt512_block_3))
  (interval_append leafTestAt512 4 6 8
  (interval_append leafTestAt512 4 5 6
  leafTestAt512_block_4
  leafTestAt512_block_5)
  (interval_append leafTestAt512 6 7 8
  leafTestAt512_block_6
  leafTestAt512_block_7)))
  (interval_append leafTestAt512 8 12 16
  (interval_append leafTestAt512 8 10 12
  (interval_append leafTestAt512 8 9 10
  leafTestAt512_block_8
  leafTestAt512_block_9)
  (interval_append leafTestAt512 10 11 12
  leafTestAt512_block_10
  leafTestAt512_block_11))
  (interval_append leafTestAt512 12 14 16
  (interval_append leafTestAt512 12 13 14
  leafTestAt512_block_12
  leafTestAt512_block_13)
  (interval_append leafTestAt512 14 15 16
  leafTestAt512_block_14
  leafTestAt512_block_15))))
  (interval_append leafTestAt512 16 24 32
  (interval_append leafTestAt512 16 20 24
  (interval_append leafTestAt512 16 18 20
  (interval_append leafTestAt512 16 17 18
  leafTestAt512_block_16
  leafTestAt512_block_17)
  (interval_append leafTestAt512 18 19 20
  leafTestAt512_block_18
  leafTestAt512_block_19))
  (interval_append leafTestAt512 20 22 24
  (interval_append leafTestAt512 20 21 22
  leafTestAt512_block_20
  leafTestAt512_block_21)
  (interval_append leafTestAt512 22 23 24
  leafTestAt512_block_22
  leafTestAt512_block_23)))
  (interval_append leafTestAt512 24 28 32
  (interval_append leafTestAt512 24 26 28
  (interval_append leafTestAt512 24 25 26
  leafTestAt512_block_24
  leafTestAt512_block_25)
  (interval_append leafTestAt512 26 27 28
  leafTestAt512_block_26
  leafTestAt512_block_27))
  (interval_append leafTestAt512 28 30 32
  (interval_append leafTestAt512 28 29 30
  leafTestAt512_block_28
  leafTestAt512_block_29)
  (interval_append leafTestAt512 30 31 32
  leafTestAt512_block_30
  leafTestAt512_block_31)))))
cert_leafInterval 512 544
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
