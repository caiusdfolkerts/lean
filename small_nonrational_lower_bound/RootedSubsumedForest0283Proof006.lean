module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0283Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0283
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 3840
cert_test_block_3 3840 0 0 16 16
cert_test_block_3 3840 1 16 32 16
cert_test_block_3 3840 2 32 48 16
cert_test_block_3 3840 3 48 64 16
cert_test_block_3 3840 4 64 80 16
cert_test_block_3 3840 5 80 96 16
cert_test_block_3 3840 6 96 112 16
cert_test_block_3 3840 7 112 128 16
cert_test_block_3 3840 8 128 144 16
cert_test_block_3 3840 9 144 160 16
cert_test_block_3 3840 10 160 176 16
cert_test_block_3 3840 11 176 185 9
theorem test3840_complete : Interval test3840 0 185 :=
  (interval_append test3840 0 96 185
  (interval_append test3840 0 48 96
  (interval_append test3840 0 16 48
  test3840_block_0
  (interval_append test3840 16 32 48
  test3840_block_1
  test3840_block_2))
  (interval_append test3840 48 64 96
  test3840_block_3
  (interval_append test3840 64 80 96
  test3840_block_4
  test3840_block_5)))
  (interval_append test3840 96 144 185
  (interval_append test3840 96 112 144
  test3840_block_6
  (interval_append test3840 112 128 144
  test3840_block_7
  test3840_block_8))
  (interval_append test3840 144 160 185
  test3840_block_9
  (interval_append test3840 160 176 185
  test3840_block_10
  test3840_block_11))))
cert_nodeInterval_3 3840 4025
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0283
