module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed015Nodes

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed015
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
cert_leafTest_block 0 0 4 4
cert_leafTest_block 1 4 8 4
cert_leafTest_block 2 8 12 4
cert_leafTest_block 3 12 16 4
cert_leafTest_block 4 16 18 2
theorem leafTest_complete : Interval leafTest 0 18 :=
  (interval_append leafTest 0 8 18
  (interval_append leafTest 0 4 8
  leafTest_block_0
  leafTest_block_1)
  (interval_append leafTest 8 12 18
  leafTest_block_2
  (interval_append leafTest 12 16 18
  leafTest_block_3
  leafTest_block_4)))
end Papers.RationalityTen.PackedReplay.PackedSevenMixed015
