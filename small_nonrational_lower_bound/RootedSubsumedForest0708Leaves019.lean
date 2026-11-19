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
cert_leafTestAt 608
cert_leafTestAt_block_2 608 0 1
cert_leafTestAt_block_2 608 1 2
cert_leafTestAt_block_2 608 2 3
cert_leafTestAt_block_2 608 3 4
cert_leafTestAt_block_2 608 4 5
cert_leafTestAt_block_2 608 5 6
cert_leafTestAt_block_2 608 6 7
cert_leafTestAt_block_2 608 7 8
cert_leafTestAt_block_2 608 8 9
cert_leafTestAt_block_2 608 9 10
cert_leafTestAt_block_2 608 10 11
cert_leafTestAt_block_2 608 11 12
cert_leafTestAt_block_2 608 12 13
cert_leafTestAt_block_2 608 13 14
cert_leafTestAt_block_2 608 14 15
cert_leafTestAt_block_2 608 15 16
cert_leafTestAt_block_2 608 16 17
cert_leafTestAt_block_2 608 17 18
cert_leafTestAt_block_2 608 18 19
cert_leafTestAt_block_2 608 19 20
cert_leafTestAt_block_2 608 20 21
cert_leafTestAt_block_2 608 21 22
cert_leafTestAt_block_2 608 22 23
cert_leafTestAt_block_2 608 23 24
cert_leafTestAt_block_2 608 24 25
cert_leafTestAt_block_2 608 25 26
cert_leafTestAt_block_2 608 26 27
cert_leafTestAt_block_2 608 27 28
cert_leafTestAt_block_2 608 28 29
cert_leafTestAt_block_2 608 29 30
cert_leafTestAt_block_2 608 30 31
cert_leafTestAt_block_2 608 31 32
theorem leafTestAt608_complete : Interval leafTestAt608 0 32 :=
  (interval_append leafTestAt608 0 16 32
  (interval_append leafTestAt608 0 8 16
  (interval_append leafTestAt608 0 4 8
  (interval_append leafTestAt608 0 2 4
  (interval_append leafTestAt608 0 1 2
  leafTestAt608_block_0
  leafTestAt608_block_1)
  (interval_append leafTestAt608 2 3 4
  leafTestAt608_block_2
  leafTestAt608_block_3))
  (interval_append leafTestAt608 4 6 8
  (interval_append leafTestAt608 4 5 6
  leafTestAt608_block_4
  leafTestAt608_block_5)
  (interval_append leafTestAt608 6 7 8
  leafTestAt608_block_6
  leafTestAt608_block_7)))
  (interval_append leafTestAt608 8 12 16
  (interval_append leafTestAt608 8 10 12
  (interval_append leafTestAt608 8 9 10
  leafTestAt608_block_8
  leafTestAt608_block_9)
  (interval_append leafTestAt608 10 11 12
  leafTestAt608_block_10
  leafTestAt608_block_11))
  (interval_append leafTestAt608 12 14 16
  (interval_append leafTestAt608 12 13 14
  leafTestAt608_block_12
  leafTestAt608_block_13)
  (interval_append leafTestAt608 14 15 16
  leafTestAt608_block_14
  leafTestAt608_block_15))))
  (interval_append leafTestAt608 16 24 32
  (interval_append leafTestAt608 16 20 24
  (interval_append leafTestAt608 16 18 20
  (interval_append leafTestAt608 16 17 18
  leafTestAt608_block_16
  leafTestAt608_block_17)
  (interval_append leafTestAt608 18 19 20
  leafTestAt608_block_18
  leafTestAt608_block_19))
  (interval_append leafTestAt608 20 22 24
  (interval_append leafTestAt608 20 21 22
  leafTestAt608_block_20
  leafTestAt608_block_21)
  (interval_append leafTestAt608 22 23 24
  leafTestAt608_block_22
  leafTestAt608_block_23)))
  (interval_append leafTestAt608 24 28 32
  (interval_append leafTestAt608 24 26 28
  (interval_append leafTestAt608 24 25 26
  leafTestAt608_block_24
  leafTestAt608_block_25)
  (interval_append leafTestAt608 26 27 28
  leafTestAt608_block_26
  leafTestAt608_block_27))
  (interval_append leafTestAt608 28 30 32
  (interval_append leafTestAt608 28 29 30
  leafTestAt608_block_28
  leafTestAt608_block_29)
  (interval_append leafTestAt608 30 31 32
  leafTestAt608_block_30
  leafTestAt608_block_31)))))
cert_leafInterval 608 640
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
