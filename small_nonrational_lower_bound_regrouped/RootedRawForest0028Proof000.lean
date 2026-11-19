module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0028Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0028
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
cert_test_block_2 0 10 320 352 32
cert_test_block_2 0 11 352 384 32
cert_test_block_2 0 12 384 406 22
theorem test0_complete : Interval test0 0 406 :=
  (interval_append test0 0 192 406
  (interval_append test0 0 96 192
  (interval_append test0 0 32 96
  test0_block_0
  (interval_append test0 32 64 96
  test0_block_1
  test0_block_2))
  (interval_append test0 96 128 192
  test0_block_3
  (interval_append test0 128 160 192
  test0_block_4
  test0_block_5)))
  (interval_append test0 192 288 406
  (interval_append test0 192 224 288
  test0_block_6
  (interval_append test0 224 256 288
  test0_block_7
  test0_block_8))
  (interval_append test0 288 352 406
  (interval_append test0 288 320 352
  test0_block_9
  test0_block_10)
  (interval_append test0 352 384 406
  test0_block_11
  test0_block_12))))
cert_nodeInterval_2 0 406
end Papers.RationalityTen.RootedForests.RootedRawForest0028
