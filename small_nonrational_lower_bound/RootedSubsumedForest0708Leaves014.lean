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
cert_leafTestAt 448
cert_leafTestAt_block_2 448 0 1
cert_leafTestAt_block_2 448 1 2
cert_leafTestAt_block_2 448 2 3
cert_leafTestAt_block_2 448 3 4
cert_leafTestAt_block_2 448 4 5
cert_leafTestAt_block_2 448 5 6
cert_leafTestAt_block_2 448 6 7
cert_leafTestAt_block_2 448 7 8
cert_leafTestAt_block_2 448 8 9
cert_leafTestAt_block_2 448 9 10
cert_leafTestAt_block_2 448 10 11
cert_leafTestAt_block_2 448 11 12
cert_leafTestAt_block_2 448 12 13
cert_leafTestAt_block_2 448 13 14
cert_leafTestAt_block_2 448 14 15
cert_leafTestAt_block_2 448 15 16
cert_leafTestAt_block_2 448 16 17
cert_leafTestAt_block_2 448 17 18
cert_leafTestAt_block_2 448 18 19
cert_leafTestAt_block_2 448 19 20
cert_leafTestAt_block_2 448 20 21
cert_leafTestAt_block_2 448 21 22
cert_leafTestAt_block_2 448 22 23
cert_leafTestAt_block_2 448 23 24
cert_leafTestAt_block_2 448 24 25
cert_leafTestAt_block_2 448 25 26
cert_leafTestAt_block_2 448 26 27
cert_leafTestAt_block_2 448 27 28
cert_leafTestAt_block_2 448 28 29
cert_leafTestAt_block_2 448 29 30
cert_leafTestAt_block_2 448 30 31
cert_leafTestAt_block_2 448 31 32
theorem leafTestAt448_complete : Interval leafTestAt448 0 32 :=
  (interval_append leafTestAt448 0 16 32
  (interval_append leafTestAt448 0 8 16
  (interval_append leafTestAt448 0 4 8
  (interval_append leafTestAt448 0 2 4
  (interval_append leafTestAt448 0 1 2
  leafTestAt448_block_0
  leafTestAt448_block_1)
  (interval_append leafTestAt448 2 3 4
  leafTestAt448_block_2
  leafTestAt448_block_3))
  (interval_append leafTestAt448 4 6 8
  (interval_append leafTestAt448 4 5 6
  leafTestAt448_block_4
  leafTestAt448_block_5)
  (interval_append leafTestAt448 6 7 8
  leafTestAt448_block_6
  leafTestAt448_block_7)))
  (interval_append leafTestAt448 8 12 16
  (interval_append leafTestAt448 8 10 12
  (interval_append leafTestAt448 8 9 10
  leafTestAt448_block_8
  leafTestAt448_block_9)
  (interval_append leafTestAt448 10 11 12
  leafTestAt448_block_10
  leafTestAt448_block_11))
  (interval_append leafTestAt448 12 14 16
  (interval_append leafTestAt448 12 13 14
  leafTestAt448_block_12
  leafTestAt448_block_13)
  (interval_append leafTestAt448 14 15 16
  leafTestAt448_block_14
  leafTestAt448_block_15))))
  (interval_append leafTestAt448 16 24 32
  (interval_append leafTestAt448 16 20 24
  (interval_append leafTestAt448 16 18 20
  (interval_append leafTestAt448 16 17 18
  leafTestAt448_block_16
  leafTestAt448_block_17)
  (interval_append leafTestAt448 18 19 20
  leafTestAt448_block_18
  leafTestAt448_block_19))
  (interval_append leafTestAt448 20 22 24
  (interval_append leafTestAt448 20 21 22
  leafTestAt448_block_20
  leafTestAt448_block_21)
  (interval_append leafTestAt448 22 23 24
  leafTestAt448_block_22
  leafTestAt448_block_23)))
  (interval_append leafTestAt448 24 28 32
  (interval_append leafTestAt448 24 26 28
  (interval_append leafTestAt448 24 25 26
  leafTestAt448_block_24
  leafTestAt448_block_25)
  (interval_append leafTestAt448 26 27 28
  leafTestAt448_block_26
  leafTestAt448_block_27))
  (interval_append leafTestAt448 28 30 32
  (interval_append leafTestAt448 28 29 30
  leafTestAt448_block_28
  leafTestAt448_block_29)
  (interval_append leafTestAt448 30 31 32
  leafTestAt448_block_30
  leafTestAt448_block_31)))))
cert_leafInterval 448 480
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
