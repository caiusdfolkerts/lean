module
prelude
public import PackedSevenMixed020Data

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed020
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
theorem kindTest_block_0 : Interval kindTest 0 1 :=
  interval_of_check kindTest 0 1 (by decide +kernel)

theorem kindTest_block_1 : Interval kindTest 1 2 :=
  interval_of_check kindTest 1 1 (by decide +kernel)

theorem kindTest_block_2 : Interval kindTest 2 3 :=
  interval_of_check kindTest 2 1 (by decide +kernel)

theorem kindTest_block_3 : Interval kindTest 3 4 :=
  interval_of_check kindTest 3 1 (by decide +kernel)

theorem kindTest_block_4 : Interval kindTest 4 5 :=
  interval_of_check kindTest 4 1 (by decide +kernel)

theorem kindTest_complete : Interval kindTest 0 5 :=
  (interval_append kindTest 0 2 5
  (interval_append kindTest 0 1 2
  kindTest_block_0
  kindTest_block_1)
  (interval_append kindTest 2 3 5
  kindTest_block_2
  (interval_append kindTest 3 4 5
  kindTest_block_3
  kindTest_block_4)))
end Papers.RationalityTen.PackedReplay.PackedSevenMixed020
