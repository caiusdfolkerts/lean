module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0026Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0026
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
cert_test_block_2 0 12 384 416 32
cert_test_block_2 0 13 416 427 11
theorem test0_complete : Interval test0 0 427 :=
  (interval_append test0 0 224 427
  (interval_append test0 0 96 224
  (interval_append test0 0 32 96
  test0_block_0
  (interval_append test0 32 64 96
  test0_block_1
  test0_block_2))
  (interval_append test0 96 160 224
  (interval_append test0 96 128 160
  test0_block_3
  test0_block_4)
  (interval_append test0 160 192 224
  test0_block_5
  test0_block_6)))
  (interval_append test0 224 320 427
  (interval_append test0 224 256 320
  test0_block_7
  (interval_append test0 256 288 320
  test0_block_8
  test0_block_9))
  (interval_append test0 320 384 427
  (interval_append test0 320 352 384
  test0_block_10
  test0_block_11)
  (interval_append test0 384 416 427
  test0_block_12
  test0_block_13))))
cert_nodeInterval_2 0 427
end Papers.RationalityTen.RootedForests.RootedRawForest0026
