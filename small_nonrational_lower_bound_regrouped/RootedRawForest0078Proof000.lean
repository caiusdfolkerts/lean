module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0078Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0078
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 0
cert_test_block_2 0 0 0 32 32
cert_test_block_2 0 1 32 64 32
cert_test_block_2 0 2 64 96 32
cert_test_block_2 0 3 96 128 32
cert_test_block_2 0 4 128 160 32
cert_test_block_2 0 5 160 192 32
cert_test_block_2 0 6 192 224 32
cert_test_block_2 0 7 224 256 32
cert_test_block_2 0 8 256 288 32
cert_test_block_2 0 9 288 320 32
cert_test_block_2 0 10 320 337 17
theorem test0_complete : Interval test0 0 337 :=
  (interval_append test0 0 160 337
  (interval_append test0 0 64 160
  (interval_append test0 0 32 64
  test0_block_0
  test0_block_1)
  (interval_append test0 64 96 160
  test0_block_2
  (interval_append test0 96 128 160
  test0_block_3
  test0_block_4)))
  (interval_append test0 160 256 337
  (interval_append test0 160 192 256
  test0_block_5
  (interval_append test0 192 224 256
  test0_block_6
  test0_block_7))
  (interval_append test0 256 288 337
  test0_block_8
  (interval_append test0 288 320 337
  test0_block_9
  test0_block_10))))
cert_nodeInterval_2 0 337
end Papers.RationalityTen.RootedForests.RootedRawForest0078
