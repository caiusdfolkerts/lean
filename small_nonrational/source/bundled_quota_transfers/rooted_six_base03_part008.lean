module
prelude
public import BundledQuotaTransfers.RootedSixBase03Part004
public import BundledQuotaTransfers.RootedSixBase03Part005
public import BundledQuotaTransfers.RootedSixBase03Part006
public import BundledQuotaTransfers.RootedSixBase03Part007

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0722Proof026. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test3328 (i : Nat) := routeTest (i + 3328)
theorem test3328_block_0 : Interval test3328 0 16 :=
  interval_of_check test3328 0 16 (by decide +kernel)

theorem test3328_block_1 : Interval test3328 16 32 :=
  interval_of_check test3328 16 16 (by decide +kernel)

theorem test3328_block_2 : Interval test3328 32 48 :=
  interval_of_check test3328 32 16 (by decide +kernel)

theorem test3328_block_3 : Interval test3328 48 64 :=
  interval_of_check test3328 48 16 (by decide +kernel)

theorem test3328_block_4 : Interval test3328 64 80 :=
  interval_of_check test3328 64 16 (by decide +kernel)

theorem test3328_block_5 : Interval test3328 80 96 :=
  interval_of_check test3328 80 16 (by decide +kernel)

theorem test3328_block_6 : Interval test3328 96 100 :=
  interval_of_check test3328 96 4 (by decide +kernel)

theorem test3328_complete : Interval test3328 0 100 :=
  (interval_append test3328 0 48 100
  (interval_append test3328 0 16 48
  test3328_block_0
  (interval_append test3328 16 32 48
  test3328_block_1
  test3328_block_2))
  (interval_append test3328 48 80 100
  (interval_append test3328 48 64 80
  test3328_block_3
  test3328_block_4)
  (interval_append test3328 80 96 100
  test3328_block_5
  test3328_block_6)))
theorem routeInterval3328 : Interval routeTest 3328 3428 := by
  intro i hlo hhi
  have h := test3328_complete (i - 3328) (Nat.zero_le _) (by omega)
  simpa only [test3328, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0722

/- Original module: RootedQuotaTransfer0722. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 3428 :=
  (interval_append routeTest 0 1664 3428
  (interval_append routeTest 0 768 1664
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
  (interval_append routeTest 768 1152 1664
  (interval_append routeTest 768 896 1152
  routeInterval768
  (interval_append routeTest 896 1024 1152
  routeInterval896
  routeInterval1024))
  (interval_append routeTest 1152 1408 1664
  (interval_append routeTest 1152 1280 1408
  routeInterval1152
  routeInterval1280)
  (interval_append routeTest 1408 1536 1664
  routeInterval1408
  routeInterval1536))))
  (interval_append routeTest 1664 2560 3428
  (interval_append routeTest 1664 2048 2560
  (interval_append routeTest 1664 1792 2048
  routeInterval1664
  (interval_append routeTest 1792 1920 2048
  routeInterval1792
  routeInterval1920))
  (interval_append routeTest 2048 2304 2560
  (interval_append routeTest 2048 2176 2304
  routeInterval2048
  routeInterval2176)
  (interval_append routeTest 2304 2432 2560
  routeInterval2304
  routeInterval2432)))
  (interval_append routeTest 2560 2944 3428
  (interval_append routeTest 2560 2688 2944
  routeInterval2560
  (interval_append routeTest 2688 2816 2944
  routeInterval2688
  routeInterval2816))
  (interval_append routeTest 2944 3200 3428
  (interval_append routeTest 2944 3072 3200
  routeInterval2944
  routeInterval3072)
  (interval_append routeTest 3200 3328 3428
  routeInterval3200
  routeInterval3328)))))

theorem disposition_checked (j : Fin 3428) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0722.quota
      ((RootedForests.RootedSubsumedForest0724.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0722.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0722.rawLeaves 644 RootedForests.RootedSubsumedForest0722.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0722.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0724.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0722
