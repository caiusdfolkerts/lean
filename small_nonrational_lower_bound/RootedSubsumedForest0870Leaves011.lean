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
cert_leafTestAt 352
cert_leafTestAt_block_2 352 0 1
cert_leafTestAt_block_2 352 1 2
cert_leafTestAt_block_2 352 2 3
cert_leafTestAt_block_2 352 3 4
cert_leafTestAt_block_2 352 4 5
cert_leafTestAt_block_2 352 5 6
cert_leafTestAt_block_2 352 6 7
cert_leafTestAt_block_2 352 7 8
cert_leafTestAt_block_2 352 8 9
cert_leafTestAt_block_2 352 9 10
cert_leafTestAt_block_2 352 10 11
cert_leafTestAt_block_2 352 11 12
cert_leafTestAt_block_2 352 12 13
cert_leafTestAt_block_2 352 13 14
cert_leafTestAt_block_2 352 14 15
cert_leafTestAt_block_2 352 15 16
cert_leafTestAt_block_2 352 16 17
cert_leafTestAt_block_2 352 17 18
cert_leafTestAt_block_2 352 18 19
cert_leafTestAt_block_2 352 19 20
cert_leafTestAt_block_2 352 20 21
cert_leafTestAt_block_2 352 21 22
cert_leafTestAt_block_2 352 22 23
cert_leafTestAt_block_2 352 23 24
cert_leafTestAt_block_2 352 24 25
cert_leafTestAt_block_2 352 25 26
cert_leafTestAt_block_2 352 26 27
cert_leafTestAt_block_2 352 27 28
cert_leafTestAt_block_2 352 28 29
cert_leafTestAt_block_2 352 29 30
cert_leafTestAt_block_2 352 30 31
cert_leafTestAt_block_2 352 31 32
theorem leafTestAt352_complete : Interval leafTestAt352 0 32 :=
  (interval_append leafTestAt352 0 16 32
  (interval_append leafTestAt352 0 8 16
  (interval_append leafTestAt352 0 4 8
  (interval_append leafTestAt352 0 2 4
  (interval_append leafTestAt352 0 1 2
  leafTestAt352_block_0
  leafTestAt352_block_1)
  (interval_append leafTestAt352 2 3 4
  leafTestAt352_block_2
  leafTestAt352_block_3))
  (interval_append leafTestAt352 4 6 8
  (interval_append leafTestAt352 4 5 6
  leafTestAt352_block_4
  leafTestAt352_block_5)
  (interval_append leafTestAt352 6 7 8
  leafTestAt352_block_6
  leafTestAt352_block_7)))
  (interval_append leafTestAt352 8 12 16
  (interval_append leafTestAt352 8 10 12
  (interval_append leafTestAt352 8 9 10
  leafTestAt352_block_8
  leafTestAt352_block_9)
  (interval_append leafTestAt352 10 11 12
  leafTestAt352_block_10
  leafTestAt352_block_11))
  (interval_append leafTestAt352 12 14 16
  (interval_append leafTestAt352 12 13 14
  leafTestAt352_block_12
  leafTestAt352_block_13)
  (interval_append leafTestAt352 14 15 16
  leafTestAt352_block_14
  leafTestAt352_block_15))))
  (interval_append leafTestAt352 16 24 32
  (interval_append leafTestAt352 16 20 24
  (interval_append leafTestAt352 16 18 20
  (interval_append leafTestAt352 16 17 18
  leafTestAt352_block_16
  leafTestAt352_block_17)
  (interval_append leafTestAt352 18 19 20
  leafTestAt352_block_18
  leafTestAt352_block_19))
  (interval_append leafTestAt352 20 22 24
  (interval_append leafTestAt352 20 21 22
  leafTestAt352_block_20
  leafTestAt352_block_21)
  (interval_append leafTestAt352 22 23 24
  leafTestAt352_block_22
  leafTestAt352_block_23)))
  (interval_append leafTestAt352 24 28 32
  (interval_append leafTestAt352 24 26 28
  (interval_append leafTestAt352 24 25 26
  leafTestAt352_block_24
  leafTestAt352_block_25)
  (interval_append leafTestAt352 26 27 28
  leafTestAt352_block_26
  leafTestAt352_block_27))
  (interval_append leafTestAt352 28 30 32
  (interval_append leafTestAt352 28 29 30
  leafTestAt352_block_28
  leafTestAt352_block_29)
  (interval_append leafTestAt352 30 31 32
  leafTestAt352_block_30
  leafTestAt352_block_31)))))
cert_leafInterval 352 384
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
