module
prelude
public import PackedSevenMixed015Nodes

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed015
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
theorem leafTest_block_0 : Interval leafTest 0 4 :=
  interval_of_check leafTest 0 4 (by decide +kernel)

theorem leafTest_block_1 : Interval leafTest 4 8 :=
  interval_of_check leafTest 4 4 (by decide +kernel)

theorem leafTest_block_2 : Interval leafTest 8 12 :=
  interval_of_check leafTest 8 4 (by decide +kernel)

theorem leafTest_block_3 : Interval leafTest 12 16 :=
  interval_of_check leafTest 12 4 (by decide +kernel)

theorem leafTest_block_4 : Interval leafTest 16 18 :=
  interval_of_check leafTest 16 2 (by decide +kernel)

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
