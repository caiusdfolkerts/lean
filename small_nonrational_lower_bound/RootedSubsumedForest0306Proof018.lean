module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0306Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 11520
cert_test_block_3 11520 0 0 16 16
cert_test_block_3 11520 1 16 32 16
cert_test_block_3 11520 2 32 48 16
cert_test_block_3 11520 3 48 64 16
cert_test_block_3 11520 4 64 80 16
cert_test_block_3 11520 5 80 96 16
cert_test_block_3 11520 6 96 112 16
cert_test_block_3 11520 7 112 128 16
cert_test_block_3 11520 8 128 144 16
cert_test_block_3 11520 9 144 160 16
cert_test_block_3 11520 10 160 176 16
cert_test_block_3 11520 11 176 192 16
cert_test_block_3 11520 12 192 199 7
theorem test11520_complete : Interval test11520 0 199 :=
  (interval_append test11520 0 96 199
  (interval_append test11520 0 48 96
  (interval_append test11520 0 16 48
  test11520_block_0
  (interval_append test11520 16 32 48
  test11520_block_1
  test11520_block_2))
  (interval_append test11520 48 64 96
  test11520_block_3
  (interval_append test11520 64 80 96
  test11520_block_4
  test11520_block_5)))
  (interval_append test11520 96 144 199
  (interval_append test11520 96 112 144
  test11520_block_6
  (interval_append test11520 112 128 144
  test11520_block_7
  test11520_block_8))
  (interval_append test11520 144 176 199
  (interval_append test11520 144 160 176
  test11520_block_9
  test11520_block_10)
  (interval_append test11520 176 192 199
  test11520_block_11
  test11520_block_12))))
cert_nodeInterval_3 11520 11719
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
