module
prelude
public import PackedSevenMixed012Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed012
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
def test640 (i : Nat) := fastTest (i + 640)
theorem test640_block_0 : Interval test640 0 32 :=
  interval_of_check test640 0 32 (by decide +kernel)

theorem test640_block_1 : Interval test640 32 64 :=
  interval_of_check test640 32 32 (by decide +kernel)

theorem test640_block_2 : Interval test640 64 96 :=
  interval_of_check test640 64 32 (by decide +kernel)

theorem test640_block_3 : Interval test640 96 128 :=
  interval_of_check test640 96 32 (by decide +kernel)

theorem test640_block_4 : Interval test640 128 160 :=
  interval_of_check test640 128 32 (by decide +kernel)

theorem test640_block_5 : Interval test640 160 192 :=
  interval_of_check test640 160 32 (by decide +kernel)

theorem test640_block_6 : Interval test640 192 224 :=
  interval_of_check test640 192 32 (by decide +kernel)

theorem test640_block_7 : Interval test640 224 228 :=
  interval_of_check test640 224 4 (by decide +kernel)

theorem test640_complete : Interval test640 0 228 :=
  (interval_append test640 0 128 228
  (interval_append test640 0 64 128
  (interval_append test640 0 32 64
  test640_block_0
  test640_block_1)
  (interval_append test640 64 96 128
  test640_block_2
  test640_block_3))
  (interval_append test640 128 192 228
  (interval_append test640 128 160 192
  test640_block_4
  test640_block_5)
  (interval_append test640 192 224 228
  test640_block_6
  test640_block_7)))
theorem nodeInterval640 : Interval fastTest 640 868 := by
  intro i hlo hhi
  have h := test640_complete (i - 640) (Nat.zero_le _) (by omega)
  simpa only [test640, Nat.sub_add_cancel hlo] using h

theorem checkedInterval640 : Interval nodeTest 640 868 := by
  intro i hlo hhi
  exact fastTest_sound i (nodeInterval640 i hlo hhi)

end Papers.RationalityTen.PackedReplay.PackedSevenMixed012
