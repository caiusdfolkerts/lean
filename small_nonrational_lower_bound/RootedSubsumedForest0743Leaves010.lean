module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0743Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 320
cert_leafTestAt_block_2 320 0 1
cert_leafTestAt_block_2 320 1 2
cert_leafTestAt_block_2 320 2 3
cert_leafTestAt_block_2 320 3 4
cert_leafTestAt_block_2 320 4 5
cert_leafTestAt_block_2 320 5 6
cert_leafTestAt_block_2 320 6 7
cert_leafTestAt_block_2 320 7 8
cert_leafTestAt_block_2 320 8 9
cert_leafTestAt_block_2 320 9 10
cert_leafTestAt_block_2 320 10 11
cert_leafTestAt_block_2 320 11 12
cert_leafTestAt_block_2 320 12 13
cert_leafTestAt_block_2 320 13 14
cert_leafTestAt_block_2 320 14 15
cert_leafTestAt_block_2 320 15 16
cert_leafTestAt_block_2 320 16 17
cert_leafTestAt_block_2 320 17 18
cert_leafTestAt_block_2 320 18 19
cert_leafTestAt_block_2 320 19 20
cert_leafTestAt_block_2 320 20 21
cert_leafTestAt_block_2 320 21 22
cert_leafTestAt_block_2 320 22 23
cert_leafTestAt_block_2 320 23 24
cert_leafTestAt_block_2 320 24 25
cert_leafTestAt_block_2 320 25 26
cert_leafTestAt_block_2 320 26 27
cert_leafTestAt_block_2 320 27 28
cert_leafTestAt_block_2 320 28 29
cert_leafTestAt_block_2 320 29 30
cert_leafTestAt_block_2 320 30 31
cert_leafTestAt_block_2 320 31 32
theorem leafTestAt320_complete : Interval leafTestAt320 0 32 :=
  (interval_append leafTestAt320 0 16 32
  (interval_append leafTestAt320 0 8 16
  (interval_append leafTestAt320 0 4 8
  (interval_append leafTestAt320 0 2 4
  (interval_append leafTestAt320 0 1 2
  leafTestAt320_block_0
  leafTestAt320_block_1)
  (interval_append leafTestAt320 2 3 4
  leafTestAt320_block_2
  leafTestAt320_block_3))
  (interval_append leafTestAt320 4 6 8
  (interval_append leafTestAt320 4 5 6
  leafTestAt320_block_4
  leafTestAt320_block_5)
  (interval_append leafTestAt320 6 7 8
  leafTestAt320_block_6
  leafTestAt320_block_7)))
  (interval_append leafTestAt320 8 12 16
  (interval_append leafTestAt320 8 10 12
  (interval_append leafTestAt320 8 9 10
  leafTestAt320_block_8
  leafTestAt320_block_9)
  (interval_append leafTestAt320 10 11 12
  leafTestAt320_block_10
  leafTestAt320_block_11))
  (interval_append leafTestAt320 12 14 16
  (interval_append leafTestAt320 12 13 14
  leafTestAt320_block_12
  leafTestAt320_block_13)
  (interval_append leafTestAt320 14 15 16
  leafTestAt320_block_14
  leafTestAt320_block_15))))
  (interval_append leafTestAt320 16 24 32
  (interval_append leafTestAt320 16 20 24
  (interval_append leafTestAt320 16 18 20
  (interval_append leafTestAt320 16 17 18
  leafTestAt320_block_16
  leafTestAt320_block_17)
  (interval_append leafTestAt320 18 19 20
  leafTestAt320_block_18
  leafTestAt320_block_19))
  (interval_append leafTestAt320 20 22 24
  (interval_append leafTestAt320 20 21 22
  leafTestAt320_block_20
  leafTestAt320_block_21)
  (interval_append leafTestAt320 22 23 24
  leafTestAt320_block_22
  leafTestAt320_block_23)))
  (interval_append leafTestAt320 24 28 32
  (interval_append leafTestAt320 24 26 28
  (interval_append leafTestAt320 24 25 26
  leafTestAt320_block_24
  leafTestAt320_block_25)
  (interval_append leafTestAt320 26 27 28
  leafTestAt320_block_26
  leafTestAt320_block_27))
  (interval_append leafTestAt320 28 30 32
  (interval_append leafTestAt320 28 29 30
  leafTestAt320_block_28
  leafTestAt320_block_29)
  (interval_append leafTestAt320 30 31 32
  leafTestAt320_block_30
  leafTestAt320_block_31)))))
cert_leafInterval 320 352
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
