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
cert_leafTestAt 416
cert_leafTestAt_block_2 416 0 1
cert_leafTestAt_block_2 416 1 2
cert_leafTestAt_block_2 416 2 3
cert_leafTestAt_block_2 416 3 4
cert_leafTestAt_block_2 416 4 5
cert_leafTestAt_block_2 416 5 6
cert_leafTestAt_block_2 416 6 7
cert_leafTestAt_block_2 416 7 8
cert_leafTestAt_block_2 416 8 9
cert_leafTestAt_block_2 416 9 10
cert_leafTestAt_block_2 416 10 11
cert_leafTestAt_block_2 416 11 12
cert_leafTestAt_block_2 416 12 13
cert_leafTestAt_block_2 416 13 14
cert_leafTestAt_block_2 416 14 15
cert_leafTestAt_block_2 416 15 16
cert_leafTestAt_block_2 416 16 17
cert_leafTestAt_block_2 416 17 18
cert_leafTestAt_block_2 416 18 19
cert_leafTestAt_block_2 416 19 20
cert_leafTestAt_block_2 416 20 21
cert_leafTestAt_block_2 416 21 22
cert_leafTestAt_block_2 416 22 23
cert_leafTestAt_block_2 416 23 24
cert_leafTestAt_block_2 416 24 25
cert_leafTestAt_block_2 416 25 26
cert_leafTestAt_block_2 416 26 27
cert_leafTestAt_block_2 416 27 28
cert_leafTestAt_block_2 416 28 29
cert_leafTestAt_block_2 416 29 30
cert_leafTestAt_block_2 416 30 31
cert_leafTestAt_block_2 416 31 32
theorem leafTestAt416_complete : Interval leafTestAt416 0 32 :=
  (interval_append leafTestAt416 0 16 32
  (interval_append leafTestAt416 0 8 16
  (interval_append leafTestAt416 0 4 8
  (interval_append leafTestAt416 0 2 4
  (interval_append leafTestAt416 0 1 2
  leafTestAt416_block_0
  leafTestAt416_block_1)
  (interval_append leafTestAt416 2 3 4
  leafTestAt416_block_2
  leafTestAt416_block_3))
  (interval_append leafTestAt416 4 6 8
  (interval_append leafTestAt416 4 5 6
  leafTestAt416_block_4
  leafTestAt416_block_5)
  (interval_append leafTestAt416 6 7 8
  leafTestAt416_block_6
  leafTestAt416_block_7)))
  (interval_append leafTestAt416 8 12 16
  (interval_append leafTestAt416 8 10 12
  (interval_append leafTestAt416 8 9 10
  leafTestAt416_block_8
  leafTestAt416_block_9)
  (interval_append leafTestAt416 10 11 12
  leafTestAt416_block_10
  leafTestAt416_block_11))
  (interval_append leafTestAt416 12 14 16
  (interval_append leafTestAt416 12 13 14
  leafTestAt416_block_12
  leafTestAt416_block_13)
  (interval_append leafTestAt416 14 15 16
  leafTestAt416_block_14
  leafTestAt416_block_15))))
  (interval_append leafTestAt416 16 24 32
  (interval_append leafTestAt416 16 20 24
  (interval_append leafTestAt416 16 18 20
  (interval_append leafTestAt416 16 17 18
  leafTestAt416_block_16
  leafTestAt416_block_17)
  (interval_append leafTestAt416 18 19 20
  leafTestAt416_block_18
  leafTestAt416_block_19))
  (interval_append leafTestAt416 20 22 24
  (interval_append leafTestAt416 20 21 22
  leafTestAt416_block_20
  leafTestAt416_block_21)
  (interval_append leafTestAt416 22 23 24
  leafTestAt416_block_22
  leafTestAt416_block_23)))
  (interval_append leafTestAt416 24 28 32
  (interval_append leafTestAt416 24 26 28
  (interval_append leafTestAt416 24 25 26
  leafTestAt416_block_24
  leafTestAt416_block_25)
  (interval_append leafTestAt416 26 27 28
  leafTestAt416_block_26
  leafTestAt416_block_27))
  (interval_append leafTestAt416 28 30 32
  (interval_append leafTestAt416 28 29 30
  leafTestAt416_block_28
  leafTestAt416_block_29)
  (interval_append leafTestAt416 30 31 32
  leafTestAt416_block_30
  leafTestAt416_block_31)))))
cert_leafInterval 416 448
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
