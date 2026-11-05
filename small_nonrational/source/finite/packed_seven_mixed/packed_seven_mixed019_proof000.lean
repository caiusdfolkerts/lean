module
prelude
public import PackedSevenMixed019Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed019
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

theorem test0_block_6 : Interval test0 192 224 :=
  interval_of_check test0 192 32 (by decide +kernel)

theorem test0_block_7 : Interval test0 224 256 :=
  interval_of_check test0 224 32 (by decide +kernel)

theorem test0_block_8 : Interval test0 256 288 :=
  interval_of_check test0 256 32 (by decide +kernel)

theorem test0_block_9 : Interval test0 288 320 :=
  interval_of_check test0 288 32 (by decide +kernel)

theorem test0_block_10 : Interval test0 320 352 :=
  interval_of_check test0 320 32 (by decide +kernel)

theorem test0_block_11 : Interval test0 352 384 :=
  interval_of_check test0 352 32 (by decide +kernel)

theorem test0_block_12 : Interval test0 384 416 :=
  interval_of_check test0 384 32 (by decide +kernel)

theorem test0_block_13 : Interval test0 416 448 :=
  interval_of_check test0 416 32 (by decide +kernel)

theorem test0_block_14 : Interval test0 448 480 :=
  interval_of_check test0 448 32 (by decide +kernel)

theorem test0_block_15 : Interval test0 480 512 :=
  interval_of_check test0 480 32 (by decide +kernel)

theorem test0_block_16 : Interval test0 512 544 :=
  interval_of_check test0 512 32 (by decide +kernel)

theorem test0_block_17 : Interval test0 544 553 :=
  interval_of_check test0 544 9 (by decide +kernel)

theorem test0_complete : Interval test0 0 553 :=
  (interval_append test0 0 288 553
  (interval_append test0 0 128 288
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  test0_block_0
  test0_block_1)
  (interval_append test0 64 96 128
  test0_block_2
  test0_block_3))
  (interval_append test0 128 192 288
  (interval_append test0 128 160 192
  test0_block_4
  test0_block_5)
  (interval_append test0 192 224 288
  test0_block_6
  (interval_append test0 224 256 288
  test0_block_7
  test0_block_8))))
  (interval_append test0 288 416 553
  (interval_append test0 288 352 416
  (interval_append test0 288 320 352
  test0_block_9
  test0_block_10)
  (interval_append test0 352 384 416
  test0_block_11
  test0_block_12))
  (interval_append test0 416 480 553
  (interval_append test0 416 448 480
  test0_block_13
  test0_block_14)
  (interval_append test0 480 512 553
  test0_block_15
  (interval_append test0 512 544 553
  test0_block_16
  test0_block_17)))))
theorem nodeInterval0 : Interval fastTest 0 553 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

theorem checkedInterval0 : Interval nodeTest 0 553 := by
  intro i hlo hhi
  exact fastTest_sound i (nodeInterval0 i hlo hhi)

end Papers.RationalityTen.PackedReplay.PackedSevenMixed019
