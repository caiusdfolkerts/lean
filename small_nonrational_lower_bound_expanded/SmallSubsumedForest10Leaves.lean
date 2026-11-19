module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest10Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTest_block_4 0 1
cert_leafTest_block_4 1 2
cert_leafTest_block_4 2 3
cert_leafTest_block_4 3 4
cert_leafTest_block_4 4 5
cert_leafTest_block_4 5 6
cert_leafTest_block_4 6 7
cert_leafTest_block_4 7 8
cert_leafTest_block_4 8 9
cert_leafTest_block_4 9 10
cert_leafTest_block_4 10 11
cert_leafTest_block_4 11 12
cert_leafTest_block_4 12 13
cert_leafTest_block_4 13 14
cert_leafTest_block_4 14 15
cert_leafTest_block_4 15 16
cert_leafTest_block_4 16 17
cert_leafTest_block_4 17 18
cert_leafTest_block_4 18 19
cert_leafTest_block_4 19 20
cert_leafTest_block_4 20 21
cert_leafTest_block_4 21 22
cert_leafTest_block_4 22 23
cert_leafTest_block_4 23 24
cert_leafTest_block_4 24 25
cert_leafTest_block_4 25 26
cert_leafTest_block_4 26 27
cert_leafTest_block_4 27 28
cert_leafTest_block_4 28 29
cert_leafTest_block_4 29 30
cert_leafTest_block_4 30 31
cert_leafTest_block_4 31 32
theorem leafTest_complete : Interval leafTest 0 32 :=
  (interval_append leafTest 0 16 32
  (interval_append leafTest 0 8 16
  (interval_append leafTest 0 4 8
  (interval_append leafTest 0 2 4
  (interval_append leafTest 0 1 2
  leafTest_block_0
  leafTest_block_1)
  (interval_append leafTest 2 3 4
  leafTest_block_2
  leafTest_block_3))
  (interval_append leafTest 4 6 8
  (interval_append leafTest 4 5 6
  leafTest_block_4
  leafTest_block_5)
  (interval_append leafTest 6 7 8
  leafTest_block_6
  leafTest_block_7)))
  (interval_append leafTest 8 12 16
  (interval_append leafTest 8 10 12
  (interval_append leafTest 8 9 10
  leafTest_block_8
  leafTest_block_9)
  (interval_append leafTest 10 11 12
  leafTest_block_10
  leafTest_block_11))
  (interval_append leafTest 12 14 16
  (interval_append leafTest 12 13 14
  leafTest_block_12
  leafTest_block_13)
  (interval_append leafTest 14 15 16
  leafTest_block_14
  leafTest_block_15))))
  (interval_append leafTest 16 24 32
  (interval_append leafTest 16 20 24
  (interval_append leafTest 16 18 20
  (interval_append leafTest 16 17 18
  leafTest_block_16
  leafTest_block_17)
  (interval_append leafTest 18 19 20
  leafTest_block_18
  leafTest_block_19))
  (interval_append leafTest 20 22 24
  (interval_append leafTest 20 21 22
  leafTest_block_20
  leafTest_block_21)
  (interval_append leafTest 22 23 24
  leafTest_block_22
  leafTest_block_23)))
  (interval_append leafTest 24 28 32
  (interval_append leafTest 24 26 28
  (interval_append leafTest 24 25 26
  leafTest_block_24
  leafTest_block_25)
  (interval_append leafTest 26 27 28
  leafTest_block_26
  leafTest_block_27))
  (interval_append leafTest 28 30 32
  (interval_append leafTest 28 29 30
  leafTest_block_28
  leafTest_block_29)
  (interval_append leafTest 30 31 32
  leafTest_block_30
  leafTest_block_31)))))
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
