module
prelude
public import BundledQuotaTransfers.RootedSixBase02Part002
public import BundledQuotaTransfers.RootedSixBase02Part003

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0364Proof008. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1024 (i : Nat) := routeTest (i + 1024)
theorem test1024_block_0 : Interval test1024 0 16 :=
  interval_of_check test1024 0 16 (by decide +kernel)

theorem test1024_block_1 : Interval test1024 16 32 :=
  interval_of_check test1024 16 16 (by decide +kernel)

theorem test1024_block_2 : Interval test1024 32 48 :=
  interval_of_check test1024 32 16 (by decide +kernel)

theorem test1024_block_3 : Interval test1024 48 64 :=
  interval_of_check test1024 48 16 (by decide +kernel)

theorem test1024_block_4 : Interval test1024 64 80 :=
  interval_of_check test1024 64 16 (by decide +kernel)

theorem test1024_block_5 : Interval test1024 80 96 :=
  interval_of_check test1024 80 16 (by decide +kernel)

theorem test1024_block_6 : Interval test1024 96 112 :=
  interval_of_check test1024 96 16 (by decide +kernel)

theorem test1024_block_7 : Interval test1024 112 128 :=
  interval_of_check test1024 112 16 (by decide +kernel)

theorem test1024_complete : Interval test1024 0 128 :=
  (interval_append test1024 0 64 128
  (interval_append test1024 0 32 64
  (interval_append test1024 0 16 32
  test1024_block_0
  test1024_block_1)
  (interval_append test1024 32 48 64
  test1024_block_2
  test1024_block_3))
  (interval_append test1024 64 96 128
  (interval_append test1024 64 80 96
  test1024_block_4
  test1024_block_5)
  (interval_append test1024 96 112 128
  test1024_block_6
  test1024_block_7)))
theorem routeInterval1024 : Interval routeTest 1024 1152 := by
  intro i hlo hhi
  have h := test1024_complete (i - 1024) (Nat.zero_le _) (by omega)
  simpa only [test1024, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof009. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1152 (i : Nat) := routeTest (i + 1152)
theorem test1152_block_0 : Interval test1152 0 16 :=
  interval_of_check test1152 0 16 (by decide +kernel)

theorem test1152_block_1 : Interval test1152 16 32 :=
  interval_of_check test1152 16 16 (by decide +kernel)

theorem test1152_block_2 : Interval test1152 32 48 :=
  interval_of_check test1152 32 16 (by decide +kernel)

theorem test1152_block_3 : Interval test1152 48 64 :=
  interval_of_check test1152 48 16 (by decide +kernel)

theorem test1152_block_4 : Interval test1152 64 80 :=
  interval_of_check test1152 64 16 (by decide +kernel)

theorem test1152_block_5 : Interval test1152 80 96 :=
  interval_of_check test1152 80 16 (by decide +kernel)

theorem test1152_block_6 : Interval test1152 96 112 :=
  interval_of_check test1152 96 16 (by decide +kernel)

theorem test1152_block_7 : Interval test1152 112 128 :=
  interval_of_check test1152 112 16 (by decide +kernel)

theorem test1152_complete : Interval test1152 0 128 :=
  (interval_append test1152 0 64 128
  (interval_append test1152 0 32 64
  (interval_append test1152 0 16 32
  test1152_block_0
  test1152_block_1)
  (interval_append test1152 32 48 64
  test1152_block_2
  test1152_block_3))
  (interval_append test1152 64 96 128
  (interval_append test1152 64 80 96
  test1152_block_4
  test1152_block_5)
  (interval_append test1152 96 112 128
  test1152_block_6
  test1152_block_7)))
theorem routeInterval1152 : Interval routeTest 1152 1280 := by
  intro i hlo hhi
  have h := test1152_complete (i - 1152) (Nat.zero_le _) (by omega)
  simpa only [test1152, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof010. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1280 (i : Nat) := routeTest (i + 1280)
theorem test1280_block_0 : Interval test1280 0 16 :=
  interval_of_check test1280 0 16 (by decide +kernel)

theorem test1280_block_1 : Interval test1280 16 32 :=
  interval_of_check test1280 16 16 (by decide +kernel)

theorem test1280_block_2 : Interval test1280 32 48 :=
  interval_of_check test1280 32 16 (by decide +kernel)

theorem test1280_block_3 : Interval test1280 48 64 :=
  interval_of_check test1280 48 16 (by decide +kernel)

theorem test1280_block_4 : Interval test1280 64 80 :=
  interval_of_check test1280 64 16 (by decide +kernel)

theorem test1280_block_5 : Interval test1280 80 96 :=
  interval_of_check test1280 80 16 (by decide +kernel)

theorem test1280_block_6 : Interval test1280 96 112 :=
  interval_of_check test1280 96 16 (by decide +kernel)

theorem test1280_block_7 : Interval test1280 112 128 :=
  interval_of_check test1280 112 16 (by decide +kernel)

theorem test1280_complete : Interval test1280 0 128 :=
  (interval_append test1280 0 64 128
  (interval_append test1280 0 32 64
  (interval_append test1280 0 16 32
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 32 48 64
  test1280_block_2
  test1280_block_3))
  (interval_append test1280 64 96 128
  (interval_append test1280 64 80 96
  test1280_block_4
  test1280_block_5)
  (interval_append test1280 96 112 128
  test1280_block_6
  test1280_block_7)))
theorem routeInterval1280 : Interval routeTest 1280 1408 := by
  intro i hlo hhi
  have h := test1280_complete (i - 1280) (Nat.zero_le _) (by omega)
  simpa only [test1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof011. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1408 (i : Nat) := routeTest (i + 1408)
theorem test1408_block_0 : Interval test1408 0 16 :=
  interval_of_check test1408 0 16 (by decide +kernel)

theorem test1408_block_1 : Interval test1408 16 32 :=
  interval_of_check test1408 16 16 (by decide +kernel)

theorem test1408_block_2 : Interval test1408 32 48 :=
  interval_of_check test1408 32 16 (by decide +kernel)

theorem test1408_block_3 : Interval test1408 48 64 :=
  interval_of_check test1408 48 16 (by decide +kernel)

theorem test1408_block_4 : Interval test1408 64 80 :=
  interval_of_check test1408 64 16 (by decide +kernel)

theorem test1408_block_5 : Interval test1408 80 96 :=
  interval_of_check test1408 80 16 (by decide +kernel)

theorem test1408_block_6 : Interval test1408 96 112 :=
  interval_of_check test1408 96 16 (by decide +kernel)

theorem test1408_block_7 : Interval test1408 112 128 :=
  interval_of_check test1408 112 16 (by decide +kernel)

theorem test1408_complete : Interval test1408 0 128 :=
  (interval_append test1408 0 64 128
  (interval_append test1408 0 32 64
  (interval_append test1408 0 16 32
  test1408_block_0
  test1408_block_1)
  (interval_append test1408 32 48 64
  test1408_block_2
  test1408_block_3))
  (interval_append test1408 64 96 128
  (interval_append test1408 64 80 96
  test1408_block_4
  test1408_block_5)
  (interval_append test1408 96 112 128
  test1408_block_6
  test1408_block_7)))
theorem routeInterval1408 : Interval routeTest 1408 1536 := by
  intro i hlo hhi
  have h := test1408_complete (i - 1408) (Nat.zero_le _) (by omega)
  simpa only [test1408, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364Proof012. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test1536 (i : Nat) := routeTest (i + 1536)
theorem test1536_block_0 : Interval test1536 0 16 :=
  interval_of_check test1536 0 16 (by decide +kernel)

theorem test1536_block_1 : Interval test1536 16 32 :=
  interval_of_check test1536 16 16 (by decide +kernel)

theorem test1536_block_2 : Interval test1536 32 48 :=
  interval_of_check test1536 32 16 (by decide +kernel)

theorem test1536_block_3 : Interval test1536 48 64 :=
  interval_of_check test1536 48 16 (by decide +kernel)

theorem test1536_block_4 : Interval test1536 64 80 :=
  interval_of_check test1536 64 16 (by decide +kernel)

theorem test1536_block_5 : Interval test1536 80 95 :=
  interval_of_check test1536 80 15 (by decide +kernel)

theorem test1536_complete : Interval test1536 0 95 :=
  (interval_append test1536 0 48 95
  (interval_append test1536 0 16 48
  test1536_block_0
  (interval_append test1536 16 32 48
  test1536_block_1
  test1536_block_2))
  (interval_append test1536 48 64 95
  test1536_block_3
  (interval_append test1536 64 80 95
  test1536_block_4
  test1536_block_5)))
theorem routeInterval1536 : Interval routeTest 1536 1631 := by
  intro i hlo hhi
  have h := test1536_complete (i - 1536) (Nat.zero_le _) (by omega)
  simpa only [test1536, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0364

/- Original module: RootedQuotaTransfer0364. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1631 :=
  (interval_append routeTest 0 768 1631
  (interval_append routeTest 0 384 768
  (interval_append routeTest 0 128 384
  routeInterval0
  (interval_append routeTest 128 256 384
  routeInterval128
  routeInterval256))
  (interval_append routeTest 384 512 768
  routeInterval384
  (interval_append routeTest 512 640 768
  routeInterval512
  routeInterval640)))
  (interval_append routeTest 768 1152 1631
  (interval_append routeTest 768 896 1152
  routeInterval768
  (interval_append routeTest 896 1024 1152
  routeInterval896
  routeInterval1024))
  (interval_append routeTest 1152 1408 1631
  (interval_append routeTest 1152 1280 1408
  routeInterval1152
  routeInterval1280)
  (interval_append routeTest 1408 1536 1631
  routeInterval1408
  routeInterval1536))))

theorem disposition_checked (j : Fin 1631) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0364.quota
      ((RootedForests.RootedSubsumedForest0708.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0364.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0364.rawLeaves 350 RootedForests.RootedSubsumedForest0364.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0364.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0708.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0364
