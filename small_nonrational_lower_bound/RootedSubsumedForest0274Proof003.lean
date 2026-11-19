module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0274Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0274
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 1920
cert_test_block_3 1920 0 0 16 16
cert_test_block_3 1920 1 16 32 16
cert_test_block_3 1920 2 32 48 16
cert_test_block_3 1920 3 48 64 16
cert_test_block_3 1920 4 64 80 16
cert_test_block_3 1920 5 80 96 16
cert_test_block_3 1920 6 96 112 16
cert_test_block_3 1920 7 112 128 16
cert_test_block_3 1920 8 128 144 16
cert_test_block_3 1920 9 144 160 16
cert_test_block_3 1920 10 160 174 14
theorem test1920_complete : Interval test1920 0 174 :=
  (interval_append test1920 0 80 174
  (interval_append test1920 0 32 80
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 80
  test1920_block_2
  (interval_append test1920 48 64 80
  test1920_block_3
  test1920_block_4)))
  (interval_append test1920 80 128 174
  (interval_append test1920 80 96 128
  test1920_block_5
  (interval_append test1920 96 112 128
  test1920_block_6
  test1920_block_7))
  (interval_append test1920 128 144 174
  test1920_block_8
  (interval_append test1920 144 160 174
  test1920_block_9
  test1920_block_10))))
cert_nodeInterval_3 1920 2094
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0274
