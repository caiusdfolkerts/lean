module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
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
cert_kindTest_block_8 0 1
cert_kindTest_block_8 1 2
cert_kindTest_block_9 2 3
cert_kindTest_block_9 3 4
cert_kindTest_block_8 4 5
cert_kindTest_block_8 5 6
cert_kindTest_block_8 6 7
cert_kindTest_block_8 7 8
cert_kindTest_block_8 8 9
cert_kindTest_block_9 9 10
cert_kindTest_block_9 10 11
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
