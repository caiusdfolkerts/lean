module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0870Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 224
cert_leafTestAt_block_2 224 0 1
cert_leafTestAt_block_2 224 1 2
cert_leafTestAt_block_2 224 2 3
cert_leafTestAt_block_2 224 3 4
cert_leafTestAt_block_2 224 4 5
cert_leafTestAt_block_2 224 5 6
cert_leafTestAt_block_2 224 6 7
cert_leafTestAt_block_2 224 7 8
cert_leafTestAt_block_2 224 8 9
cert_leafTestAt_block_2 224 9 10
cert_leafTestAt_block_2 224 10 11
cert_leafTestAt_block_2 224 11 12
cert_leafTestAt_block_2 224 12 13
cert_leafTestAt_block_2 224 13 14
cert_leafTestAt_block_2 224 14 15
cert_leafTestAt_block_2 224 15 16
cert_leafTestAt_block_2 224 16 17
cert_leafTestAt_block_2 224 17 18
cert_leafTestAt_block_2 224 18 19
cert_leafTestAt_block_2 224 19 20
cert_leafTestAt_block_2 224 20 21
cert_leafTestAt_block_2 224 21 22
cert_leafTestAt_block_2 224 22 23
cert_leafTestAt_block_2 224 23 24
cert_leafTestAt_block_2 224 24 25
cert_leafTestAt_block_2 224 25 26
cert_leafTestAt_block_2 224 26 27
cert_leafTestAt_block_2 224 27 28
cert_leafTestAt_block_2 224 28 29
cert_leafTestAt_block_2 224 29 30
cert_leafTestAt_block_2 224 30 31
cert_leafTestAt_block_2 224 31 32
theorem leafTestAt224_complete : Interval leafTestAt224 0 32 :=
  (interval_append leafTestAt224 0 16 32
  (interval_append leafTestAt224 0 8 16
  (interval_append leafTestAt224 0 4 8
  (interval_append leafTestAt224 0 2 4
  (interval_append leafTestAt224 0 1 2
  leafTestAt224_block_0
  leafTestAt224_block_1)
  (interval_append leafTestAt224 2 3 4
  leafTestAt224_block_2
  leafTestAt224_block_3))
  (interval_append leafTestAt224 4 6 8
  (interval_append leafTestAt224 4 5 6
  leafTestAt224_block_4
  leafTestAt224_block_5)
  (interval_append leafTestAt224 6 7 8
  leafTestAt224_block_6
  leafTestAt224_block_7)))
  (interval_append leafTestAt224 8 12 16
  (interval_append leafTestAt224 8 10 12
  (interval_append leafTestAt224 8 9 10
  leafTestAt224_block_8
  leafTestAt224_block_9)
  (interval_append leafTestAt224 10 11 12
  leafTestAt224_block_10
  leafTestAt224_block_11))
  (interval_append leafTestAt224 12 14 16
  (interval_append leafTestAt224 12 13 14
  leafTestAt224_block_12
  leafTestAt224_block_13)
  (interval_append leafTestAt224 14 15 16
  leafTestAt224_block_14
  leafTestAt224_block_15))))
  (interval_append leafTestAt224 16 24 32
  (interval_append leafTestAt224 16 20 24
  (interval_append leafTestAt224 16 18 20
  (interval_append leafTestAt224 16 17 18
  leafTestAt224_block_16
  leafTestAt224_block_17)
  (interval_append leafTestAt224 18 19 20
  leafTestAt224_block_18
  leafTestAt224_block_19))
  (interval_append leafTestAt224 20 22 24
  (interval_append leafTestAt224 20 21 22
  leafTestAt224_block_20
  leafTestAt224_block_21)
  (interval_append leafTestAt224 22 23 24
  leafTestAt224_block_22
  leafTestAt224_block_23)))
  (interval_append leafTestAt224 24 28 32
  (interval_append leafTestAt224 24 26 28
  (interval_append leafTestAt224 24 25 26
  leafTestAt224_block_24
  leafTestAt224_block_25)
  (interval_append leafTestAt224 26 27 28
  leafTestAt224_block_26
  leafTestAt224_block_27))
  (interval_append leafTestAt224 28 30 32
  (interval_append leafTestAt224 28 29 30
  leafTestAt224_block_28
  leafTestAt224_block_29)
  (interval_append leafTestAt224 30 31 32
  leafTestAt224_block_30
  leafTestAt224_block_31)))))
cert_leafInterval 224 256
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
