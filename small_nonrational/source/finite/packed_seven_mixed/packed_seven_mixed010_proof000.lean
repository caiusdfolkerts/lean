module
prelude
public import PackedSevenMixed010Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed010
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
def test0 (i : Nat) := fastTest (i + 0)
theorem test0_block_0 : Interval test0 0 32 :=
  interval_of_check test0 0 32 (by decide +kernel)

theorem test0_block_1 : Interval test0 32 64 :=
  interval_of_check test0 32 32 (by decide +kernel)

theorem test0_block_2 : Interval test0 64 96 :=
  interval_of_check test0 64 32 (by decide +kernel)

theorem test0_block_3 : Interval test0 96 128 :=
  interval_of_check test0 96 32 (by decide +kernel)

theorem test0_block_4 : Interval test0 128 160 :=
  interval_of_check test0 128 32 (by decide +kernel)

theorem test0_block_5 : Interval test0 160 192 :=
  interval_of_check test0 160 32 (by decide +kernel)

theorem test0_block_6 : Interval test0 192 196 :=
  interval_of_check test0 192 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 196 :=
  (interval_append test0 0 96 196
  (interval_append test0 0 32 96
  test0_block_0
  (interval_append test0 32 64 96
  test0_block_1
  test0_block_2))
  (interval_append test0 96 160 196
  (interval_append test0 96 128 160
  test0_block_3
  test0_block_4)
  (interval_append test0 160 192 196
  test0_block_5
  test0_block_6)))
theorem nodeInterval0 : Interval fastTest 0 196 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

theorem checkedInterval0 : Interval nodeTest 0 196 := by
  intro i hlo hhi
  exact fastTest_sound i (nodeInterval0 i hlo hhi)

end Papers.RationalityTen.PackedReplay.PackedSevenMixed010
