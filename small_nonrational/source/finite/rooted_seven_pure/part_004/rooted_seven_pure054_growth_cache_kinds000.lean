module
prelude
public import RootedSevenPure054GrowthCacheData
public import RootedSevenPure054GrowthCacheKindSupport3

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure054
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def kindTest_0 (i : Nat) := kindTest (i+0)
theorem kindTest_0_block_0 : Interval kindTest_0 0 1 :=
  interval_of_check kindTest_0 0 1 (by decide +kernel)

theorem kindTest_0_block_1 : Interval kindTest_0 1 2 :=
  interval_of_check kindTest_0 1 1 (by decide +kernel)

theorem kindTest_0_block_2 : Interval kindTest_0 2 3 :=
  interval_of_check kindTest_0 2 1 (by decide +kernel)

theorem kindTest_0_block_3 : Interval kindTest_0 3 4 := by
  intro i hlo hhi
  have h : i = 3 := by omega
  subst i
  exact kindTest_large_3

theorem kindTest_0_block_4 : Interval kindTest_0 4 5 :=
  interval_of_check kindTest_0 4 1 (by decide +kernel)

theorem kindTest_0_complete : Interval kindTest_0 0 5 :=
  (interval_append kindTest_0 0 2 5
  (interval_append kindTest_0 0 1 2
  kindTest_0_block_0
  kindTest_0_block_1)
  (interval_append kindTest_0 2 3 5
  kindTest_0_block_2
  (interval_append kindTest_0 3 4 5
  kindTest_0_block_3
  kindTest_0_block_4)))
theorem kindTestInterval0 : Interval kindTest 0 5 := by
  intro i hlo hhi
  have h := kindTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [kindTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure054
