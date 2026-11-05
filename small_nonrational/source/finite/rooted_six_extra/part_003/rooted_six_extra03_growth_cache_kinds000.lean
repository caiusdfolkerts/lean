module
prelude
public import RootedSixExtra03GrowthCacheData
public import RootedSixExtra03GrowthCacheKindSupport2
public import RootedSixExtra03GrowthCacheKindSupport3
public import RootedSixExtra03GrowthCacheKindSupport9
public import RootedSixExtra03GrowthCacheKindSupport10

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra03
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def kindTest_0 (i : Nat) := kindTest (i+0)
theorem kindTest_0_block_0 : Interval kindTest_0 0 1 :=
  interval_of_check kindTest_0 0 1 (by decide +kernel)

theorem kindTest_0_block_1 : Interval kindTest_0 1 2 :=
  interval_of_check kindTest_0 1 1 (by decide +kernel)

theorem kindTest_0_block_2 : Interval kindTest_0 2 3 := by
  intro i hlo hhi
  have h : i = 2 := by omega
  subst i
  exact kindTest_large_2

theorem kindTest_0_block_3 : Interval kindTest_0 3 4 := by
  intro i hlo hhi
  have h : i = 3 := by omega
  subst i
  exact kindTest_large_3

theorem kindTest_0_block_4 : Interval kindTest_0 4 5 :=
  interval_of_check kindTest_0 4 1 (by decide +kernel)

theorem kindTest_0_block_5 : Interval kindTest_0 5 6 :=
  interval_of_check kindTest_0 5 1 (by decide +kernel)

theorem kindTest_0_block_6 : Interval kindTest_0 6 7 :=
  interval_of_check kindTest_0 6 1 (by decide +kernel)

theorem kindTest_0_block_7 : Interval kindTest_0 7 8 :=
  interval_of_check kindTest_0 7 1 (by decide +kernel)

theorem kindTest_0_block_8 : Interval kindTest_0 8 9 :=
  interval_of_check kindTest_0 8 1 (by decide +kernel)

theorem kindTest_0_block_9 : Interval kindTest_0 9 10 := by
  intro i hlo hhi
  have h : i = 9 := by omega
  subst i
  exact kindTest_large_9

theorem kindTest_0_block_10 : Interval kindTest_0 10 11 := by
  intro i hlo hhi
  have h : i = 10 := by omega
  subst i
  exact kindTest_large_10

theorem kindTest_0_complete : Interval kindTest_0 0 11 :=
  (interval_append kindTest_0 0 5 11
  (interval_append kindTest_0 0 2 5
  (interval_append kindTest_0 0 1 2
  kindTest_0_block_0
  kindTest_0_block_1)
  (interval_append kindTest_0 2 3 5
  kindTest_0_block_2
  (interval_append kindTest_0 3 4 5
  kindTest_0_block_3
  kindTest_0_block_4)))
  (interval_append kindTest_0 5 8 11
  (interval_append kindTest_0 5 6 8
  kindTest_0_block_5
  (interval_append kindTest_0 6 7 8
  kindTest_0_block_6
  kindTest_0_block_7))
  (interval_append kindTest_0 8 9 11
  kindTest_0_block_8
  (interval_append kindTest_0 9 10 11
  kindTest_0_block_9
  kindTest_0_block_10))))
theorem kindTestInterval0 : Interval kindTest 0 11 := by
  intro i hlo hhi
  have h := kindTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [kindTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
