module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0781Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0781
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 0
cert_test_block_3 0 0 0 16 16
cert_test_block_3 0 1 16 32 16
cert_test_block_3 0 2 32 48 16
cert_test_block_3 0 3 48 64 16
cert_test_block_3 0 4 64 80 16
cert_test_block_3 0 5 80 96 16
cert_test_block_3 0 6 96 112 16
cert_test_block_3 0 7 112 128 16
cert_test_block_3 0 8 128 144 16
cert_test_block_3 0 9 144 160 16
cert_test_block_3 0 10 160 170 10
theorem test0_complete : Interval test0 0 170 :=
  (interval_append test0 0 80 170
  (interval_append test0 0 32 80
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 80
  test0_block_2
  (interval_append test0 48 64 80
  test0_block_3
  test0_block_4)))
  (interval_append test0 80 128 170
  (interval_append test0 80 96 128
  test0_block_5
  (interval_append test0 96 112 128
  test0_block_6
  test0_block_7))
  (interval_append test0 128 144 170
  test0_block_8
  (interval_append test0 144 160 170
  test0_block_9
  test0_block_10))))
cert_nodeInterval_3 0 170
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0781
