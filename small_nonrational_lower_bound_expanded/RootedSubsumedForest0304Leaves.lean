module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0304Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0304
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTest_block_3 0 1
cert_leafTest_block_3 1 2
cert_leafTest_block_3 2 3
cert_leafTest_block_3 3 4
cert_leafTest_block_3 4 5
cert_leafTest_block_3 5 6
cert_leafTest_block_3 6 7
cert_leafTest_block_3 7 8
cert_leafTest_block_3 8 9
cert_leafTest_block_3 9 10
cert_leafTest_block_3 10 11
cert_leafTest_block_3 11 12
cert_leafTest_block_3 12 13
cert_leafTest_block_3 13 14
cert_leafTest_block_3 14 15
cert_leafTest_block_3 15 16
cert_leafTest_block_3 16 17
cert_leafTest_block_3 17 18
cert_leafTest_block_3 18 19
cert_leafTest_block_3 19 20
theorem leafTest_complete : Interval leafTest 0 20 :=
  (interval_append leafTest 0 10 20
  (interval_append leafTest 0 5 10
  (interval_append leafTest 0 2 5
  (interval_append leafTest 0 1 2
  leafTest_block_0
  leafTest_block_1)
  (interval_append leafTest 2 3 5
  leafTest_block_2
  (interval_append leafTest 3 4 5
  leafTest_block_3
  leafTest_block_4)))
  (interval_append leafTest 5 7 10
  (interval_append leafTest 5 6 7
  leafTest_block_5
  leafTest_block_6)
  (interval_append leafTest 7 8 10
  leafTest_block_7
  (interval_append leafTest 8 9 10
  leafTest_block_8
  leafTest_block_9))))
  (interval_append leafTest 10 15 20
  (interval_append leafTest 10 12 15
  (interval_append leafTest 10 11 12
  leafTest_block_10
  leafTest_block_11)
  (interval_append leafTest 12 13 15
  leafTest_block_12
  (interval_append leafTest 13 14 15
  leafTest_block_13
  leafTest_block_14)))
  (interval_append leafTest 15 17 20
  (interval_append leafTest 15 16 17
  leafTest_block_15
  leafTest_block_16)
  (interval_append leafTest 17 18 20
  leafTest_block_17
  (interval_append leafTest 18 19 20
  leafTest_block_18
  leafTest_block_19)))))
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0304
