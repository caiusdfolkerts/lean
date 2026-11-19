module
prelude
public import BundledQuotaTransfers.RootedSixBase01Part005
public import BundledQuotaTransfers.RootedSixBase01Part006
public import BundledQuotaTransfers.RootedSixBase01Part007
public import BundledQuotaTransfers.RootedSixBase01Part008

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0353Proof024. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test3072 (i : Nat) := routeTest (i + 3072)
theorem test3072_block_0 : Interval test3072 0 16 :=
  interval_of_check test3072 0 16 (by decide +kernel)

theorem test3072_block_1 : Interval test3072 16 32 :=
  interval_of_check test3072 16 16 (by decide +kernel)

theorem test3072_block_2 : Interval test3072 32 48 :=
  interval_of_check test3072 32 16 (by decide +kernel)

theorem test3072_block_3 : Interval test3072 48 64 :=
  interval_of_check test3072 48 16 (by decide +kernel)

theorem test3072_block_4 : Interval test3072 64 80 :=
  interval_of_check test3072 64 16 (by decide +kernel)

theorem test3072_block_5 : Interval test3072 80 96 :=
  interval_of_check test3072 80 16 (by decide +kernel)

theorem test3072_block_6 : Interval test3072 96 112 :=
  interval_of_check test3072 96 16 (by decide +kernel)

theorem test3072_block_7 : Interval test3072 112 128 :=
  interval_of_check test3072 112 16 (by decide +kernel)

theorem test3072_complete : Interval test3072 0 128 :=
  (interval_append test3072 0 64 128
  (interval_append test3072 0 32 64
  (interval_append test3072 0 16 32
  test3072_block_0
  test3072_block_1)
  (interval_append test3072 32 48 64
  test3072_block_2
  test3072_block_3))
  (interval_append test3072 64 96 128
  (interval_append test3072 64 80 96
  test3072_block_4
  test3072_block_5)
  (interval_append test3072 96 112 128
  test3072_block_6
  test3072_block_7)))
theorem routeInterval3072 : Interval routeTest 3072 3200 := by
  intro i hlo hhi
  have h := test3072_complete (i - 3072) (Nat.zero_le _) (by omega)
  simpa only [test3072, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof025. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test3200 (i : Nat) := routeTest (i + 3200)
theorem test3200_block_0 : Interval test3200 0 16 :=
  interval_of_check test3200 0 16 (by decide +kernel)

theorem test3200_block_1 : Interval test3200 16 32 :=
  interval_of_check test3200 16 16 (by decide +kernel)

theorem test3200_block_2 : Interval test3200 32 48 :=
  interval_of_check test3200 32 16 (by decide +kernel)

theorem test3200_block_3 : Interval test3200 48 64 :=
  interval_of_check test3200 48 16 (by decide +kernel)

theorem test3200_block_4 : Interval test3200 64 80 :=
  interval_of_check test3200 64 16 (by decide +kernel)

theorem test3200_block_5 : Interval test3200 80 96 :=
  interval_of_check test3200 80 16 (by decide +kernel)

theorem test3200_block_6 : Interval test3200 96 112 :=
  interval_of_check test3200 96 16 (by decide +kernel)

theorem test3200_block_7 : Interval test3200 112 128 :=
  interval_of_check test3200 112 16 (by decide +kernel)

theorem test3200_complete : Interval test3200 0 128 :=
  (interval_append test3200 0 64 128
  (interval_append test3200 0 32 64
  (interval_append test3200 0 16 32
  test3200_block_0
  test3200_block_1)
  (interval_append test3200 32 48 64
  test3200_block_2
  test3200_block_3))
  (interval_append test3200 64 96 128
  (interval_append test3200 64 80 96
  test3200_block_4
  test3200_block_5)
  (interval_append test3200 96 112 128
  test3200_block_6
  test3200_block_7)))
theorem routeInterval3200 : Interval routeTest 3200 3328 := by
  intro i hlo hhi
  have h := test3200_complete (i - 3200) (Nat.zero_le _) (by omega)
  simpa only [test3200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof026. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
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

theorem test3328_block_6 : Interval test3328 96 112 :=
  interval_of_check test3328 96 16 (by decide +kernel)

theorem test3328_block_7 : Interval test3328 112 128 :=
  interval_of_check test3328 112 16 (by decide +kernel)

theorem test3328_complete : Interval test3328 0 128 :=
  (interval_append test3328 0 64 128
  (interval_append test3328 0 32 64
  (interval_append test3328 0 16 32
  test3328_block_0
  test3328_block_1)
  (interval_append test3328 32 48 64
  test3328_block_2
  test3328_block_3))
  (interval_append test3328 64 96 128
  (interval_append test3328 64 80 96
  test3328_block_4
  test3328_block_5)
  (interval_append test3328 96 112 128
  test3328_block_6
  test3328_block_7)))
theorem routeInterval3328 : Interval routeTest 3328 3456 := by
  intro i hlo hhi
  have h := test3328_complete (i - 3328) (Nat.zero_le _) (by omega)
  simpa only [test3328, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof027. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test3456 (i : Nat) := routeTest (i + 3456)
theorem test3456_block_0 : Interval test3456 0 16 :=
  interval_of_check test3456 0 16 (by decide +kernel)

theorem test3456_block_1 : Interval test3456 16 32 :=
  interval_of_check test3456 16 16 (by decide +kernel)

theorem test3456_block_2 : Interval test3456 32 48 :=
  interval_of_check test3456 32 16 (by decide +kernel)

theorem test3456_block_3 : Interval test3456 48 64 :=
  interval_of_check test3456 48 16 (by decide +kernel)

theorem test3456_block_4 : Interval test3456 64 80 :=
  interval_of_check test3456 64 16 (by decide +kernel)

theorem test3456_block_5 : Interval test3456 80 96 :=
  interval_of_check test3456 80 16 (by decide +kernel)

theorem test3456_block_6 : Interval test3456 96 112 :=
  interval_of_check test3456 96 16 (by decide +kernel)

theorem test3456_block_7 : Interval test3456 112 128 :=
  interval_of_check test3456 112 16 (by decide +kernel)

theorem test3456_complete : Interval test3456 0 128 :=
  (interval_append test3456 0 64 128
  (interval_append test3456 0 32 64
  (interval_append test3456 0 16 32
  test3456_block_0
  test3456_block_1)
  (interval_append test3456 32 48 64
  test3456_block_2
  test3456_block_3))
  (interval_append test3456 64 96 128
  (interval_append test3456 64 80 96
  test3456_block_4
  test3456_block_5)
  (interval_append test3456 96 112 128
  test3456_block_6
  test3456_block_7)))
theorem routeInterval3456 : Interval routeTest 3456 3584 := by
  intro i hlo hhi
  have h := test3456_complete (i - 3456) (Nat.zero_le _) (by omega)
  simpa only [test3456, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof028. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test3584 (i : Nat) := routeTest (i + 3584)
theorem test3584_block_0 : Interval test3584 0 16 :=
  interval_of_check test3584 0 16 (by decide +kernel)

theorem test3584_block_1 : Interval test3584 16 32 :=
  interval_of_check test3584 16 16 (by decide +kernel)

theorem test3584_block_2 : Interval test3584 32 48 :=
  interval_of_check test3584 32 16 (by decide +kernel)

theorem test3584_block_3 : Interval test3584 48 64 :=
  interval_of_check test3584 48 16 (by decide +kernel)

theorem test3584_block_4 : Interval test3584 64 80 :=
  interval_of_check test3584 64 16 (by decide +kernel)

theorem test3584_block_5 : Interval test3584 80 96 :=
  interval_of_check test3584 80 16 (by decide +kernel)

theorem test3584_block_6 : Interval test3584 96 112 :=
  interval_of_check test3584 96 16 (by decide +kernel)

theorem test3584_block_7 : Interval test3584 112 128 :=
  interval_of_check test3584 112 16 (by decide +kernel)

theorem test3584_complete : Interval test3584 0 128 :=
  (interval_append test3584 0 64 128
  (interval_append test3584 0 32 64
  (interval_append test3584 0 16 32
  test3584_block_0
  test3584_block_1)
  (interval_append test3584 32 48 64
  test3584_block_2
  test3584_block_3))
  (interval_append test3584 64 96 128
  (interval_append test3584 64 80 96
  test3584_block_4
  test3584_block_5)
  (interval_append test3584 96 112 128
  test3584_block_6
  test3584_block_7)))
theorem routeInterval3584 : Interval routeTest 3584 3712 := by
  intro i hlo hhi
  have h := test3584_complete (i - 3584) (Nat.zero_le _) (by omega)
  simpa only [test3584, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof029. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test3712 (i : Nat) := routeTest (i + 3712)
theorem test3712_block_0 : Interval test3712 0 16 :=
  interval_of_check test3712 0 16 (by decide +kernel)

theorem test3712_block_1 : Interval test3712 16 32 :=
  interval_of_check test3712 16 16 (by decide +kernel)

theorem test3712_block_2 : Interval test3712 32 48 :=
  interval_of_check test3712 32 16 (by decide +kernel)

theorem test3712_block_3 : Interval test3712 48 64 :=
  interval_of_check test3712 48 16 (by decide +kernel)

theorem test3712_block_4 : Interval test3712 64 80 :=
  interval_of_check test3712 64 16 (by decide +kernel)

theorem test3712_block_5 : Interval test3712 80 96 :=
  interval_of_check test3712 80 16 (by decide +kernel)

theorem test3712_block_6 : Interval test3712 96 112 :=
  interval_of_check test3712 96 16 (by decide +kernel)

theorem test3712_block_7 : Interval test3712 112 128 :=
  interval_of_check test3712 112 16 (by decide +kernel)

theorem test3712_complete : Interval test3712 0 128 :=
  (interval_append test3712 0 64 128
  (interval_append test3712 0 32 64
  (interval_append test3712 0 16 32
  test3712_block_0
  test3712_block_1)
  (interval_append test3712 32 48 64
  test3712_block_2
  test3712_block_3))
  (interval_append test3712 64 96 128
  (interval_append test3712 64 80 96
  test3712_block_4
  test3712_block_5)
  (interval_append test3712 96 112 128
  test3712_block_6
  test3712_block_7)))
theorem routeInterval3712 : Interval routeTest 3712 3840 := by
  intro i hlo hhi
  have h := test3712_complete (i - 3712) (Nat.zero_le _) (by omega)
  simpa only [test3712, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof030. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test3840 (i : Nat) := routeTest (i + 3840)
theorem test3840_block_0 : Interval test3840 0 16 :=
  interval_of_check test3840 0 16 (by decide +kernel)

theorem test3840_block_1 : Interval test3840 16 32 :=
  interval_of_check test3840 16 16 (by decide +kernel)

theorem test3840_block_2 : Interval test3840 32 48 :=
  interval_of_check test3840 32 16 (by decide +kernel)

theorem test3840_block_3 : Interval test3840 48 64 :=
  interval_of_check test3840 48 16 (by decide +kernel)

theorem test3840_block_4 : Interval test3840 64 80 :=
  interval_of_check test3840 64 16 (by decide +kernel)

theorem test3840_block_5 : Interval test3840 80 96 :=
  interval_of_check test3840 80 16 (by decide +kernel)

theorem test3840_block_6 : Interval test3840 96 112 :=
  interval_of_check test3840 96 16 (by decide +kernel)

theorem test3840_block_7 : Interval test3840 112 128 :=
  interval_of_check test3840 112 16 (by decide +kernel)

theorem test3840_complete : Interval test3840 0 128 :=
  (interval_append test3840 0 64 128
  (interval_append test3840 0 32 64
  (interval_append test3840 0 16 32
  test3840_block_0
  test3840_block_1)
  (interval_append test3840 32 48 64
  test3840_block_2
  test3840_block_3))
  (interval_append test3840 64 96 128
  (interval_append test3840 64 80 96
  test3840_block_4
  test3840_block_5)
  (interval_append test3840 96 112 128
  test3840_block_6
  test3840_block_7)))
theorem routeInterval3840 : Interval routeTest 3840 3968 := by
  intro i hlo hhi
  have h := test3840_complete (i - 3840) (Nat.zero_le _) (by omega)
  simpa only [test3840, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353Proof031. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test3968 (i : Nat) := routeTest (i + 3968)
theorem test3968_block_0 : Interval test3968 0 16 :=
  interval_of_check test3968 0 16 (by decide +kernel)

theorem test3968_block_1 : Interval test3968 16 32 :=
  interval_of_check test3968 16 16 (by decide +kernel)

theorem test3968_block_2 : Interval test3968 32 48 :=
  interval_of_check test3968 32 16 (by decide +kernel)

theorem test3968_block_3 : Interval test3968 48 64 :=
  interval_of_check test3968 48 16 (by decide +kernel)

theorem test3968_block_4 : Interval test3968 64 80 :=
  interval_of_check test3968 64 16 (by decide +kernel)

theorem test3968_block_5 : Interval test3968 80 96 :=
  interval_of_check test3968 80 16 (by decide +kernel)

theorem test3968_block_6 : Interval test3968 96 112 :=
  interval_of_check test3968 96 16 (by decide +kernel)

theorem test3968_block_7 : Interval test3968 112 116 :=
  interval_of_check test3968 112 4 (by decide +kernel)

theorem test3968_complete : Interval test3968 0 116 :=
  (interval_append test3968 0 64 116
  (interval_append test3968 0 32 64
  (interval_append test3968 0 16 32
  test3968_block_0
  test3968_block_1)
  (interval_append test3968 32 48 64
  test3968_block_2
  test3968_block_3))
  (interval_append test3968 64 96 116
  (interval_append test3968 64 80 96
  test3968_block_4
  test3968_block_5)
  (interval_append test3968 96 112 116
  test3968_block_6
  test3968_block_7)))
theorem routeInterval3968 : Interval routeTest 3968 4084 := by
  intro i hlo hhi
  have h := test3968_complete (i - 3968) (Nat.zero_le _) (by omega)
  simpa only [test3968, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0353

/- Original module: RootedQuotaTransfer0353. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4084 :=
  (interval_append routeTest 0 2048 4084
  (interval_append routeTest 0 1024 2048
  (interval_append routeTest 0 512 1024
  (interval_append routeTest 0 256 512
  (interval_append routeTest 0 128 256
  routeInterval0
  routeInterval128)
  (interval_append routeTest 256 384 512
  routeInterval256
  routeInterval384))
  (interval_append routeTest 512 768 1024
  (interval_append routeTest 512 640 768
  routeInterval512
  routeInterval640)
  (interval_append routeTest 768 896 1024
  routeInterval768
  routeInterval896)))
  (interval_append routeTest 1024 1536 2048
  (interval_append routeTest 1024 1280 1536
  (interval_append routeTest 1024 1152 1280
  routeInterval1024
  routeInterval1152)
  (interval_append routeTest 1280 1408 1536
  routeInterval1280
  routeInterval1408))
  (interval_append routeTest 1536 1792 2048
  (interval_append routeTest 1536 1664 1792
  routeInterval1536
  routeInterval1664)
  (interval_append routeTest 1792 1920 2048
  routeInterval1792
  routeInterval1920))))
  (interval_append routeTest 2048 3072 4084
  (interval_append routeTest 2048 2560 3072
  (interval_append routeTest 2048 2304 2560
  (interval_append routeTest 2048 2176 2304
  routeInterval2048
  routeInterval2176)
  (interval_append routeTest 2304 2432 2560
  routeInterval2304
  routeInterval2432))
  (interval_append routeTest 2560 2816 3072
  (interval_append routeTest 2560 2688 2816
  routeInterval2560
  routeInterval2688)
  (interval_append routeTest 2816 2944 3072
  routeInterval2816
  routeInterval2944)))
  (interval_append routeTest 3072 3584 4084
  (interval_append routeTest 3072 3328 3584
  (interval_append routeTest 3072 3200 3328
  routeInterval3072
  routeInterval3200)
  (interval_append routeTest 3328 3456 3584
  routeInterval3328
  routeInterval3456))
  (interval_append routeTest 3584 3840 4084
  (interval_append routeTest 3584 3712 3840
  routeInterval3584
  routeInterval3712)
  (interval_append routeTest 3840 3968 4084
  routeInterval3840
  routeInterval3968)))))

theorem disposition_checked (j : Fin 4084) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0353.quota
      ((RootedForests.RootedSubsumedForest0355.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0353.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0353.rawLeaves 756 RootedForests.RootedSubsumedForest0353.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0353.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0355.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0353
