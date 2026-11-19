module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0063Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0063
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTest_block_2 0 1
cert_leafTest_block_2 1 2
cert_leafTest_block_2 2 3
cert_leafTest_block_2 3 4
cert_leafTest_block_2 4 5
cert_leafTest_block_2 5 6
cert_leafTest_block_2 6 7
cert_leafTest_block_2 7 8
cert_leafTest_block_2 8 9
cert_leafTest_block_2 9 10
cert_leafTest_block_2 10 11
cert_leafTest_block_2 11 12
cert_leafTest_block_2 12 13
cert_leafTest_block_2 13 14
cert_leafTest_block_2 14 15
cert_leafTest_block_2 15 16
cert_leafTest_block_2 16 17
cert_leafTest_block_2 17 18
theorem leafTest_complete : Interval leafTest 0 18 :=
  (interval_append leafTest 0 9 18
  (interval_append leafTest 0 4 9
  (interval_append leafTest 0 2 4
  (interval_append leafTest 0 1 2
  leafTest_block_0
  leafTest_block_1)
  (interval_append leafTest 2 3 4
  leafTest_block_2
  leafTest_block_3))
  (interval_append leafTest 4 6 9
  (interval_append leafTest 4 5 6
  leafTest_block_4
  leafTest_block_5)
  (interval_append leafTest 6 7 9
  leafTest_block_6
  (interval_append leafTest 7 8 9
  leafTest_block_7
  leafTest_block_8))))
  (interval_append leafTest 9 13 18
  (interval_append leafTest 9 11 13
  (interval_append leafTest 9 10 11
  leafTest_block_9
  leafTest_block_10)
  (interval_append leafTest 11 12 13
  leafTest_block_11
  leafTest_block_12))
  (interval_append leafTest 13 15 18
  (interval_append leafTest 13 14 15
  leafTest_block_13
  leafTest_block_14)
  (interval_append leafTest 15 16 18
  leafTest_block_15
  (interval_append leafTest 16 17 18
  leafTest_block_16
  leafTest_block_17)))))
end Papers.RationalityTen.RootedForests.RootedRawForest0063
