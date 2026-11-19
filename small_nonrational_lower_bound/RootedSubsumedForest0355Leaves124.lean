module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0355Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 3968
cert_leafTestAt_block_2 3968 0 1
cert_leafTestAt_block_2 3968 1 2
cert_leafTestAt_block_2 3968 2 3
cert_leafTestAt_block_2 3968 3 4
cert_leafTestAt_block_2 3968 4 5
cert_leafTestAt_block_2 3968 5 6
cert_leafTestAt_block_2 3968 6 7
cert_leafTestAt_block_2 3968 7 8
cert_leafTestAt_block_2 3968 8 9
cert_leafTestAt_block_2 3968 9 10
cert_leafTestAt_block_2 3968 10 11
cert_leafTestAt_block_2 3968 11 12
cert_leafTestAt_block_2 3968 12 13
cert_leafTestAt_block_2 3968 13 14
cert_leafTestAt_block_2 3968 14 15
cert_leafTestAt_block_2 3968 15 16
cert_leafTestAt_block_2 3968 16 17
cert_leafTestAt_block_2 3968 17 18
cert_leafTestAt_block_2 3968 18 19
cert_leafTestAt_block_2 3968 19 20
cert_leafTestAt_block_2 3968 20 21
cert_leafTestAt_block_2 3968 21 22
cert_leafTestAt_block_2 3968 22 23
cert_leafTestAt_block_2 3968 23 24
cert_leafTestAt_block_2 3968 24 25
cert_leafTestAt_block_2 3968 25 26
cert_leafTestAt_block_2 3968 26 27
cert_leafTestAt_block_2 3968 27 28
cert_leafTestAt_block_2 3968 28 29
cert_leafTestAt_block_2 3968 29 30
cert_leafTestAt_block_2 3968 30 31
cert_leafTestAt_block_2 3968 31 32
theorem leafTestAt3968_complete : Interval leafTestAt3968 0 32 :=
  (interval_append leafTestAt3968 0 16 32
  (interval_append leafTestAt3968 0 8 16
  (interval_append leafTestAt3968 0 4 8
  (interval_append leafTestAt3968 0 2 4
  (interval_append leafTestAt3968 0 1 2
  leafTestAt3968_block_0
  leafTestAt3968_block_1)
  (interval_append leafTestAt3968 2 3 4
  leafTestAt3968_block_2
  leafTestAt3968_block_3))
  (interval_append leafTestAt3968 4 6 8
  (interval_append leafTestAt3968 4 5 6
  leafTestAt3968_block_4
  leafTestAt3968_block_5)
  (interval_append leafTestAt3968 6 7 8
  leafTestAt3968_block_6
  leafTestAt3968_block_7)))
  (interval_append leafTestAt3968 8 12 16
  (interval_append leafTestAt3968 8 10 12
  (interval_append leafTestAt3968 8 9 10
  leafTestAt3968_block_8
  leafTestAt3968_block_9)
  (interval_append leafTestAt3968 10 11 12
  leafTestAt3968_block_10
  leafTestAt3968_block_11))
  (interval_append leafTestAt3968 12 14 16
  (interval_append leafTestAt3968 12 13 14
  leafTestAt3968_block_12
  leafTestAt3968_block_13)
  (interval_append leafTestAt3968 14 15 16
  leafTestAt3968_block_14
  leafTestAt3968_block_15))))
  (interval_append leafTestAt3968 16 24 32
  (interval_append leafTestAt3968 16 20 24
  (interval_append leafTestAt3968 16 18 20
  (interval_append leafTestAt3968 16 17 18
  leafTestAt3968_block_16
  leafTestAt3968_block_17)
  (interval_append leafTestAt3968 18 19 20
  leafTestAt3968_block_18
  leafTestAt3968_block_19))
  (interval_append leafTestAt3968 20 22 24
  (interval_append leafTestAt3968 20 21 22
  leafTestAt3968_block_20
  leafTestAt3968_block_21)
  (interval_append leafTestAt3968 22 23 24
  leafTestAt3968_block_22
  leafTestAt3968_block_23)))
  (interval_append leafTestAt3968 24 28 32
  (interval_append leafTestAt3968 24 26 28
  (interval_append leafTestAt3968 24 25 26
  leafTestAt3968_block_24
  leafTestAt3968_block_25)
  (interval_append leafTestAt3968 26 27 28
  leafTestAt3968_block_26
  leafTestAt3968_block_27))
  (interval_append leafTestAt3968 28 30 32
  (interval_append leafTestAt3968 28 29 30
  leafTestAt3968_block_28
  leafTestAt3968_block_29)
  (interval_append leafTestAt3968 30 31 32
  leafTestAt3968_block_30
  leafTestAt3968_block_31)))))
cert_leafInterval 3968 4000
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
