module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed015Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed015
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
cert_test_4 1280
cert_test_block 1280 0 0 32 32
cert_test_block 1280 1 32 64 32
cert_test_block 1280 2 64 96 32
cert_test_block 1280 3 96 128 32
cert_test_block 1280 4 128 160 32
cert_test_block 1280 5 160 192 32
cert_test_block 1280 6 192 224 32
cert_test_block 1280 7 224 256 32
cert_test_block 1280 8 256 288 32
cert_test_block 1280 9 288 295 7
theorem test1280_complete : Interval test1280 0 295 :=
  (interval_append test1280 0 160 295
  (interval_append test1280 0 64 160
  (interval_append test1280 0 32 64
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 64 96 160
  test1280_block_2
  (interval_append test1280 96 128 160
  test1280_block_3
  test1280_block_4)))
  (interval_append test1280 160 224 295
  (interval_append test1280 160 192 224
  test1280_block_5
  test1280_block_6)
  (interval_append test1280 224 256 295
  test1280_block_7
  (interval_append test1280 256 288 295
  test1280_block_8
  test1280_block_9))))
cert_nodeInterval 1280 1575
cert_checkedInterval 1280 1575
end Papers.RationalityTen.PackedReplay.PackedSevenMixed015
