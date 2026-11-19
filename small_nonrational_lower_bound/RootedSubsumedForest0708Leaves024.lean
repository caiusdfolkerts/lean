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
cert_leafTestAt 768
cert_leafTestAt_block_2 768 0 1
cert_leafTestAt_block_2 768 1 2
cert_leafTestAt_block_2 768 2 3
cert_leafTestAt_block_2 768 3 4
cert_leafTestAt_block_2 768 4 5
cert_leafTestAt_block_2 768 5 6
cert_leafTestAt_block_2 768 6 7
cert_leafTestAt_block_2 768 7 8
cert_leafTestAt_block_2 768 8 9
cert_leafTestAt_block_2 768 9 10
cert_leafTestAt_block_2 768 10 11
cert_leafTestAt_block_2 768 11 12
cert_leafTestAt_block_2 768 12 13
cert_leafTestAt_block_2 768 13 14
cert_leafTestAt_block_2 768 14 15
cert_leafTestAt_block_2 768 15 16
cert_leafTestAt_block_2 768 16 17
cert_leafTestAt_block_2 768 17 18
cert_leafTestAt_block_2 768 18 19
cert_leafTestAt_block_2 768 19 20
cert_leafTestAt_block_2 768 20 21
cert_leafTestAt_block_2 768 21 22
cert_leafTestAt_block_2 768 22 23
cert_leafTestAt_block_2 768 23 24
cert_leafTestAt_block_2 768 24 25
cert_leafTestAt_block_2 768 25 26
cert_leafTestAt_block_2 768 26 27
cert_leafTestAt_block_2 768 27 28
cert_leafTestAt_block_2 768 28 29
cert_leafTestAt_block_2 768 29 30
cert_leafTestAt_block_2 768 30 31
cert_leafTestAt_block_2 768 31 32
theorem leafTestAt768_complete : Interval leafTestAt768 0 32 :=
  (interval_append leafTestAt768 0 16 32
  (interval_append leafTestAt768 0 8 16
  (interval_append leafTestAt768 0 4 8
  (interval_append leafTestAt768 0 2 4
  (interval_append leafTestAt768 0 1 2
  leafTestAt768_block_0
  leafTestAt768_block_1)
  (interval_append leafTestAt768 2 3 4
  leafTestAt768_block_2
  leafTestAt768_block_3))
  (interval_append leafTestAt768 4 6 8
  (interval_append leafTestAt768 4 5 6
  leafTestAt768_block_4
  leafTestAt768_block_5)
  (interval_append leafTestAt768 6 7 8
  leafTestAt768_block_6
  leafTestAt768_block_7)))
  (interval_append leafTestAt768 8 12 16
  (interval_append leafTestAt768 8 10 12
  (interval_append leafTestAt768 8 9 10
  leafTestAt768_block_8
  leafTestAt768_block_9)
  (interval_append leafTestAt768 10 11 12
  leafTestAt768_block_10
  leafTestAt768_block_11))
  (interval_append leafTestAt768 12 14 16
  (interval_append leafTestAt768 12 13 14
  leafTestAt768_block_12
  leafTestAt768_block_13)
  (interval_append leafTestAt768 14 15 16
  leafTestAt768_block_14
  leafTestAt768_block_15))))
  (interval_append leafTestAt768 16 24 32
  (interval_append leafTestAt768 16 20 24
  (interval_append leafTestAt768 16 18 20
  (interval_append leafTestAt768 16 17 18
  leafTestAt768_block_16
  leafTestAt768_block_17)
  (interval_append leafTestAt768 18 19 20
  leafTestAt768_block_18
  leafTestAt768_block_19))
  (interval_append leafTestAt768 20 22 24
  (interval_append leafTestAt768 20 21 22
  leafTestAt768_block_20
  leafTestAt768_block_21)
  (interval_append leafTestAt768 22 23 24
  leafTestAt768_block_22
  leafTestAt768_block_23)))
  (interval_append leafTestAt768 24 28 32
  (interval_append leafTestAt768 24 26 28
  (interval_append leafTestAt768 24 25 26
  leafTestAt768_block_24
  leafTestAt768_block_25)
  (interval_append leafTestAt768 26 27 28
  leafTestAt768_block_26
  leafTestAt768_block_27))
  (interval_append leafTestAt768 28 30 32
  (interval_append leafTestAt768 28 29 30
  leafTestAt768_block_28
  leafTestAt768_block_29)
  (interval_append leafTestAt768 30 31 32
  leafTestAt768_block_30
  leafTestAt768_block_31)))))
cert_leafInterval 768 800
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
