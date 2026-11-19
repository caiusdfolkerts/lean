module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0320Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 160
cert_leafTestAt_block_2 160 0 1
cert_leafTestAt_block_2 160 1 2
cert_leafTestAt_block_2 160 2 3
cert_leafTestAt_block_2 160 3 4
cert_leafTestAt_block_2 160 4 5
cert_leafTestAt_block_2 160 5 6
cert_leafTestAt_block_2 160 6 7
cert_leafTestAt_block_2 160 7 8
cert_leafTestAt_block_2 160 8 9
cert_leafTestAt_block_2 160 9 10
cert_leafTestAt_block_2 160 10 11
cert_leafTestAt_block_2 160 11 12
cert_leafTestAt_block_2 160 12 13
cert_leafTestAt_block_2 160 13 14
cert_leafTestAt_block_2 160 14 15
cert_leafTestAt_block_2 160 15 16
cert_leafTestAt_block_2 160 16 17
cert_leafTestAt_block_2 160 17 18
cert_leafTestAt_block_2 160 18 19
cert_leafTestAt_block_2 160 19 20
cert_leafTestAt_block_2 160 20 21
cert_leafTestAt_block_2 160 21 22
cert_leafTestAt_block_2 160 22 23
cert_leafTestAt_block_2 160 23 24
cert_leafTestAt_block_2 160 24 25
cert_leafTestAt_block_2 160 25 26
cert_leafTestAt_block_2 160 26 27
cert_leafTestAt_block_2 160 27 28
cert_leafTestAt_block_2 160 28 29
cert_leafTestAt_block_2 160 29 30
cert_leafTestAt_block_2 160 30 31
cert_leafTestAt_block_2 160 31 32
theorem leafTestAt160_complete : Interval leafTestAt160 0 32 :=
  (interval_append leafTestAt160 0 16 32
  (interval_append leafTestAt160 0 8 16
  (interval_append leafTestAt160 0 4 8
  (interval_append leafTestAt160 0 2 4
  (interval_append leafTestAt160 0 1 2
  leafTestAt160_block_0
  leafTestAt160_block_1)
  (interval_append leafTestAt160 2 3 4
  leafTestAt160_block_2
  leafTestAt160_block_3))
  (interval_append leafTestAt160 4 6 8
  (interval_append leafTestAt160 4 5 6
  leafTestAt160_block_4
  leafTestAt160_block_5)
  (interval_append leafTestAt160 6 7 8
  leafTestAt160_block_6
  leafTestAt160_block_7)))
  (interval_append leafTestAt160 8 12 16
  (interval_append leafTestAt160 8 10 12
  (interval_append leafTestAt160 8 9 10
  leafTestAt160_block_8
  leafTestAt160_block_9)
  (interval_append leafTestAt160 10 11 12
  leafTestAt160_block_10
  leafTestAt160_block_11))
  (interval_append leafTestAt160 12 14 16
  (interval_append leafTestAt160 12 13 14
  leafTestAt160_block_12
  leafTestAt160_block_13)
  (interval_append leafTestAt160 14 15 16
  leafTestAt160_block_14
  leafTestAt160_block_15))))
  (interval_append leafTestAt160 16 24 32
  (interval_append leafTestAt160 16 20 24
  (interval_append leafTestAt160 16 18 20
  (interval_append leafTestAt160 16 17 18
  leafTestAt160_block_16
  leafTestAt160_block_17)
  (interval_append leafTestAt160 18 19 20
  leafTestAt160_block_18
  leafTestAt160_block_19))
  (interval_append leafTestAt160 20 22 24
  (interval_append leafTestAt160 20 21 22
  leafTestAt160_block_20
  leafTestAt160_block_21)
  (interval_append leafTestAt160 22 23 24
  leafTestAt160_block_22
  leafTestAt160_block_23)))
  (interval_append leafTestAt160 24 28 32
  (interval_append leafTestAt160 24 26 28
  (interval_append leafTestAt160 24 25 26
  leafTestAt160_block_24
  leafTestAt160_block_25)
  (interval_append leafTestAt160 26 27 28
  leafTestAt160_block_26
  leafTestAt160_block_27))
  (interval_append leafTestAt160 28 30 32
  (interval_append leafTestAt160 28 29 30
  leafTestAt160_block_28
  leafTestAt160_block_29)
  (interval_append leafTestAt160 30 31 32
  leafTestAt160_block_30
  leafTestAt160_block_31)))))
cert_leafInterval 160 192
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
