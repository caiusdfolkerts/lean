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
cert_leafTestAt 480
cert_leafTestAt_block_2 480 0 1
cert_leafTestAt_block_2 480 1 2
cert_leafTestAt_block_2 480 2 3
cert_leafTestAt_block_2 480 3 4
cert_leafTestAt_block_2 480 4 5
cert_leafTestAt_block_2 480 5 6
cert_leafTestAt_block_2 480 6 7
cert_leafTestAt_block_2 480 7 8
cert_leafTestAt_block_2 480 8 9
cert_leafTestAt_block_2 480 9 10
cert_leafTestAt_block_2 480 10 11
cert_leafTestAt_block_2 480 11 12
cert_leafTestAt_block_2 480 12 13
cert_leafTestAt_block_2 480 13 14
cert_leafTestAt_block_2 480 14 15
cert_leafTestAt_block_2 480 15 16
cert_leafTestAt_block_2 480 16 17
cert_leafTestAt_block_2 480 17 18
cert_leafTestAt_block_2 480 18 19
cert_leafTestAt_block_2 480 19 20
cert_leafTestAt_block_2 480 20 21
cert_leafTestAt_block_2 480 21 22
cert_leafTestAt_block_2 480 22 23
cert_leafTestAt_block_2 480 23 24
cert_leafTestAt_block_2 480 24 25
cert_leafTestAt_block_2 480 25 26
cert_leafTestAt_block_2 480 26 27
cert_leafTestAt_block_2 480 27 28
cert_leafTestAt_block_2 480 28 29
cert_leafTestAt_block_2 480 29 30
cert_leafTestAt_block_2 480 30 31
cert_leafTestAt_block_2 480 31 32
theorem leafTestAt480_complete : Interval leafTestAt480 0 32 :=
  (interval_append leafTestAt480 0 16 32
  (interval_append leafTestAt480 0 8 16
  (interval_append leafTestAt480 0 4 8
  (interval_append leafTestAt480 0 2 4
  (interval_append leafTestAt480 0 1 2
  leafTestAt480_block_0
  leafTestAt480_block_1)
  (interval_append leafTestAt480 2 3 4
  leafTestAt480_block_2
  leafTestAt480_block_3))
  (interval_append leafTestAt480 4 6 8
  (interval_append leafTestAt480 4 5 6
  leafTestAt480_block_4
  leafTestAt480_block_5)
  (interval_append leafTestAt480 6 7 8
  leafTestAt480_block_6
  leafTestAt480_block_7)))
  (interval_append leafTestAt480 8 12 16
  (interval_append leafTestAt480 8 10 12
  (interval_append leafTestAt480 8 9 10
  leafTestAt480_block_8
  leafTestAt480_block_9)
  (interval_append leafTestAt480 10 11 12
  leafTestAt480_block_10
  leafTestAt480_block_11))
  (interval_append leafTestAt480 12 14 16
  (interval_append leafTestAt480 12 13 14
  leafTestAt480_block_12
  leafTestAt480_block_13)
  (interval_append leafTestAt480 14 15 16
  leafTestAt480_block_14
  leafTestAt480_block_15))))
  (interval_append leafTestAt480 16 24 32
  (interval_append leafTestAt480 16 20 24
  (interval_append leafTestAt480 16 18 20
  (interval_append leafTestAt480 16 17 18
  leafTestAt480_block_16
  leafTestAt480_block_17)
  (interval_append leafTestAt480 18 19 20
  leafTestAt480_block_18
  leafTestAt480_block_19))
  (interval_append leafTestAt480 20 22 24
  (interval_append leafTestAt480 20 21 22
  leafTestAt480_block_20
  leafTestAt480_block_21)
  (interval_append leafTestAt480 22 23 24
  leafTestAt480_block_22
  leafTestAt480_block_23)))
  (interval_append leafTestAt480 24 28 32
  (interval_append leafTestAt480 24 26 28
  (interval_append leafTestAt480 24 25 26
  leafTestAt480_block_24
  leafTestAt480_block_25)
  (interval_append leafTestAt480 26 27 28
  leafTestAt480_block_26
  leafTestAt480_block_27))
  (interval_append leafTestAt480 28 30 32
  (interval_append leafTestAt480 28 29 30
  leafTestAt480_block_28
  leafTestAt480_block_29)
  (interval_append leafTestAt480 30 31 32
  leafTestAt480_block_30
  leafTestAt480_block_31)))))
cert_leafInterval 480 512
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
