module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0723Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0723
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 16000
cert_test_block_3 16000 0 0 16 16
cert_test_block_3 16000 1 16 32 16
cert_test_block_3 16000 2 32 48 16
cert_test_block_3 16000 3 48 64 16
cert_test_block_3 16000 4 64 80 16
cert_test_block_3 16000 5 80 96 16
cert_test_block_3 16000 6 96 112 16
cert_test_block_3 16000 7 112 128 16
cert_test_block_3 16000 8 128 144 16
cert_test_block_3 16000 9 144 160 16
cert_test_block_3 16000 10 160 176 16
cert_test_block_3 16000 11 176 182 6
theorem test16000_complete : Interval test16000 0 182 :=
  (interval_append test16000 0 96 182
  (interval_append test16000 0 48 96
  (interval_append test16000 0 16 48
  test16000_block_0
  (interval_append test16000 16 32 48
  test16000_block_1
  test16000_block_2))
  (interval_append test16000 48 64 96
  test16000_block_3
  (interval_append test16000 64 80 96
  test16000_block_4
  test16000_block_5)))
  (interval_append test16000 96 144 182
  (interval_append test16000 96 112 144
  test16000_block_6
  (interval_append test16000 112 128 144
  test16000_block_7
  test16000_block_8))
  (interval_append test16000 144 160 182
  test16000_block_9
  (interval_append test16000 160 176 182
  test16000_block_10
  test16000_block_11))))
cert_nodeInterval_3 16000 16182
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0723
