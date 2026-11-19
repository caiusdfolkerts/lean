module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed020Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed020
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
cert_test_4 0
cert_test_block 0 0 0 32 32
cert_test_block 0 1 32 64 32
cert_test_block 0 2 64 96 32
cert_test_block 0 3 96 128 32
cert_test_block 0 4 128 160 32
cert_test_block 0 5 160 192 32
cert_test_block 0 6 192 224 32
cert_test_block 0 7 224 256 32
cert_test_block 0 8 256 288 32
cert_test_block 0 9 288 320 32
cert_test_block 0 10 320 352 32
cert_test_block 0 11 352 373 21
theorem test0_complete : Interval test0 0 373 :=
  (interval_append test0 0 192 373
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
  (interval_append test0 192 288 373
  (interval_append test0 192 224 288
  test0_block_6
  (interval_append test0 224 256 288
  test0_block_7
  test0_block_8))
  (interval_append test0 288 320 373
  test0_block_9
  (interval_append test0 320 352 373
  test0_block_10
  test0_block_11))))
cert_nodeInterval 0 373
cert_checkedInterval 0 373
end Papers.RationalityTen.PackedReplay.PackedSevenMixed020
