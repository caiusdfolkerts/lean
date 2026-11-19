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
cert_leafTestAt 896
cert_leafTestAt_block_2 896 0 1
cert_leafTestAt_block_2 896 1 2
cert_leafTestAt_block_2 896 2 3
cert_leafTestAt_block_2 896 3 4
cert_leafTestAt_block_2 896 4 5
cert_leafTestAt_block_2 896 5 6
cert_leafTestAt_block_2 896 6 7
cert_leafTestAt_block_2 896 7 8
cert_leafTestAt_block_2 896 8 9
cert_leafTestAt_block_2 896 9 10
cert_leafTestAt_block_2 896 10 11
cert_leafTestAt_block_2 896 11 12
cert_leafTestAt_block_2 896 12 13
cert_leafTestAt_block_2 896 13 14
cert_leafTestAt_block_2 896 14 15
cert_leafTestAt_block_2 896 15 16
cert_leafTestAt_block_2 896 16 17
cert_leafTestAt_block_2 896 17 18
cert_leafTestAt_block_2 896 18 19
cert_leafTestAt_block_2 896 19 20
cert_leafTestAt_block_2 896 20 21
cert_leafTestAt_block_2 896 21 22
cert_leafTestAt_block_2 896 22 23
cert_leafTestAt_block_2 896 23 24
cert_leafTestAt_block_2 896 24 25
cert_leafTestAt_block_2 896 25 26
cert_leafTestAt_block_2 896 26 27
cert_leafTestAt_block_2 896 27 28
cert_leafTestAt_block_2 896 28 29
cert_leafTestAt_block_2 896 29 30
cert_leafTestAt_block_2 896 30 31
cert_leafTestAt_block_2 896 31 32
theorem leafTestAt896_complete : Interval leafTestAt896 0 32 :=
  (interval_append leafTestAt896 0 16 32
  (interval_append leafTestAt896 0 8 16
  (interval_append leafTestAt896 0 4 8
  (interval_append leafTestAt896 0 2 4
  (interval_append leafTestAt896 0 1 2
  leafTestAt896_block_0
  leafTestAt896_block_1)
  (interval_append leafTestAt896 2 3 4
  leafTestAt896_block_2
  leafTestAt896_block_3))
  (interval_append leafTestAt896 4 6 8
  (interval_append leafTestAt896 4 5 6
  leafTestAt896_block_4
  leafTestAt896_block_5)
  (interval_append leafTestAt896 6 7 8
  leafTestAt896_block_6
  leafTestAt896_block_7)))
  (interval_append leafTestAt896 8 12 16
  (interval_append leafTestAt896 8 10 12
  (interval_append leafTestAt896 8 9 10
  leafTestAt896_block_8
  leafTestAt896_block_9)
  (interval_append leafTestAt896 10 11 12
  leafTestAt896_block_10
  leafTestAt896_block_11))
  (interval_append leafTestAt896 12 14 16
  (interval_append leafTestAt896 12 13 14
  leafTestAt896_block_12
  leafTestAt896_block_13)
  (interval_append leafTestAt896 14 15 16
  leafTestAt896_block_14
  leafTestAt896_block_15))))
  (interval_append leafTestAt896 16 24 32
  (interval_append leafTestAt896 16 20 24
  (interval_append leafTestAt896 16 18 20
  (interval_append leafTestAt896 16 17 18
  leafTestAt896_block_16
  leafTestAt896_block_17)
  (interval_append leafTestAt896 18 19 20
  leafTestAt896_block_18
  leafTestAt896_block_19))
  (interval_append leafTestAt896 20 22 24
  (interval_append leafTestAt896 20 21 22
  leafTestAt896_block_20
  leafTestAt896_block_21)
  (interval_append leafTestAt896 22 23 24
  leafTestAt896_block_22
  leafTestAt896_block_23)))
  (interval_append leafTestAt896 24 28 32
  (interval_append leafTestAt896 24 26 28
  (interval_append leafTestAt896 24 25 26
  leafTestAt896_block_24
  leafTestAt896_block_25)
  (interval_append leafTestAt896 26 27 28
  leafTestAt896_block_26
  leafTestAt896_block_27))
  (interval_append leafTestAt896 28 30 32
  (interval_append leafTestAt896 28 29 30
  leafTestAt896_block_28
  leafTestAt896_block_29)
  (interval_append leafTestAt896 30 31 32
  leafTestAt896_block_30
  leafTestAt896_block_31)))))
cert_leafInterval 896 928
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
