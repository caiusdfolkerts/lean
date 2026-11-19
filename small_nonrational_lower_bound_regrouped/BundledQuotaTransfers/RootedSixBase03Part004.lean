module
prelude
public import BundledQuotaTransfers.RootedSixBase03Part001
public import BundledQuotaTransfers.RootedSixBase03Part002
public import BundledQuotaTransfers.RootedSixBase03Part003
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0719Dispositions
public import RootedSubsumedForest0723Data
public import RootedSubsumedForest0722Dispositions
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0717Proof022. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test2816 (i : Nat) := routeTest (i + 2816)
theorem test2816_block_0 : Interval test2816 0 16 :=
  interval_of_check test2816 0 16 (by decide +kernel)

theorem test2816_block_1 : Interval test2816 16 32 :=
  interval_of_check test2816 16 16 (by decide +kernel)

theorem test2816_block_2 : Interval test2816 32 48 :=
  interval_of_check test2816 32 16 (by decide +kernel)

theorem test2816_block_3 : Interval test2816 48 64 :=
  interval_of_check test2816 48 16 (by decide +kernel)

theorem test2816_block_4 : Interval test2816 64 80 :=
  interval_of_check test2816 64 16 (by decide +kernel)

theorem test2816_block_5 : Interval test2816 80 96 :=
  interval_of_check test2816 80 16 (by decide +kernel)

theorem test2816_block_6 : Interval test2816 96 112 :=
  interval_of_check test2816 96 16 (by decide +kernel)

theorem test2816_block_7 : Interval test2816 112 128 :=
  interval_of_check test2816 112 16 (by decide +kernel)

theorem test2816_complete : Interval test2816 0 128 :=
  (interval_append test2816 0 64 128
  (interval_append test2816 0 32 64
  (interval_append test2816 0 16 32
  test2816_block_0
  test2816_block_1)
  (interval_append test2816 32 48 64
  test2816_block_2
  test2816_block_3))
  (interval_append test2816 64 96 128
  (interval_append test2816 64 80 96
  test2816_block_4
  test2816_block_5)
  (interval_append test2816 96 112 128
  test2816_block_6
  test2816_block_7)))
theorem routeInterval2816 : Interval routeTest 2816 2944 := by
  intro i hlo hhi
  have h := test2816_complete (i - 2816) (Nat.zero_le _) (by omega)
  simpa only [test2816, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof023. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test2944 (i : Nat) := routeTest (i + 2944)
theorem test2944_block_0 : Interval test2944 0 16 :=
  interval_of_check test2944 0 16 (by decide +kernel)

theorem test2944_block_1 : Interval test2944 16 32 :=
  interval_of_check test2944 16 16 (by decide +kernel)

theorem test2944_block_2 : Interval test2944 32 48 :=
  interval_of_check test2944 32 16 (by decide +kernel)

theorem test2944_block_3 : Interval test2944 48 64 :=
  interval_of_check test2944 48 16 (by decide +kernel)

theorem test2944_block_4 : Interval test2944 64 80 :=
  interval_of_check test2944 64 16 (by decide +kernel)

theorem test2944_block_5 : Interval test2944 80 96 :=
  interval_of_check test2944 80 16 (by decide +kernel)

theorem test2944_block_6 : Interval test2944 96 112 :=
  interval_of_check test2944 96 16 (by decide +kernel)

theorem test2944_block_7 : Interval test2944 112 128 :=
  interval_of_check test2944 112 16 (by decide +kernel)

theorem test2944_complete : Interval test2944 0 128 :=
  (interval_append test2944 0 64 128
  (interval_append test2944 0 32 64
  (interval_append test2944 0 16 32
  test2944_block_0
  test2944_block_1)
  (interval_append test2944 32 48 64
  test2944_block_2
  test2944_block_3))
  (interval_append test2944 64 96 128
  (interval_append test2944 64 80 96
  test2944_block_4
  test2944_block_5)
  (interval_append test2944 96 112 128
  test2944_block_6
  test2944_block_7)))
theorem routeInterval2944 : Interval routeTest 2944 3072 := by
  intro i hlo hhi
  have h := test2944_complete (i - 2944) (Nat.zero_le _) (by omega)
  simpa only [test2944, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof024. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof025. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof026. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
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
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0717.quota
      ((RootedForests.RootedSubsumedForest0724.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0717.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0717.rawLeaves 92 RootedForests.RootedSubsumedForest0717.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0717.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0724.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0719Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0719
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 719: use the complete forest for case 723, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0719.quota k ≤ RootedForests.RootedSubsumedForest0723.quota k := by
  match k with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | 3 => decide +kernel
  | 4 => decide +kernel
  | 5 => decide +kernel
  | 6 => decide +kernel
  | 7 => decide +kernel
  | 8 => decide +kernel
  | 9 => decide +kernel
  | 10 => decide +kernel
  | n + 11 => exact Nat.le_refl 0

def routes : Table Route :=
(.branch 73
 (.branch 36
 (.branch 18
 (.branch 9
 (.branch 4
 (.leaf (.quota 1))
 (.branch 6
 (.branch 5
 (.leaf (.reuse 0))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 27
 (.leaf (.quota 1))
 (.branch 31
 (.leaf (.quota 1))
 (.branch 33
 (.branch 32
 (.leaf (.reuse 1))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 49
 (.branch 47
 (.leaf (.quota 1))
 (.branch 48
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 109
 (.branch 91
 (.leaf (.quota 1))
 (.branch 100
 (.branch 95
 (.leaf (.quota 1))
 (.branch 97
 (.leaf (.quota 1))
 (.branch 98
 (.leaf (.quota 1))
 (.branch 99
 (.leaf (.reuse 4))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1))))
 (.branch 127
 (.leaf (.quota 1))
 (.branch 136
 (.branch 131
 (.leaf (.quota 1))
 (.branch 133
 (.leaf (.quota 1))
 (.branch 134
 (.leaf (.quota 1))
 (.branch 135
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 141
 (.leaf (.quota 1))
 (.branch 143
 (.branch 142
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 144
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0719.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0719.rawLeaves 8 (RootedForests.RootedSubsumedForest0723.rawLeaves i) (routes.get i)

def disposition (j : Fin 146) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0719.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0719

/- Original module: RootedQuotaTransfer0719Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0719
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_complete : Interval test0 0 128 :=
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 128
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 128
  test0_block_6
  test0_block_7)))
theorem routeInterval0 : Interval routeTest 0 128 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0719

/- Original module: RootedQuotaTransfer0719Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0719
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 18 :=
  interval_of_check test128 16 2 (by decide +kernel)

theorem test128_complete : Interval test128 0 18 :=
  (interval_append test128 0 16 18
  test128_block_0
  test128_block_1)
theorem routeInterval128 : Interval routeTest 128 146 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0719

/- Original module: RootedQuotaTransfer0719. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0719
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 146 :=
  (interval_append routeTest 0 128 146
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 146) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0719.quota
      ((RootedForests.RootedSubsumedForest0723.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0719.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0719.rawLeaves 8 RootedForests.RootedSubsumedForest0719.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0719.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0723.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0719

/- Original module: RootedQuotaTransfer0722Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 722: use the complete forest for case 724, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0722.quota k ≤ RootedForests.RootedSubsumedForest0724.quota k := by
  match k with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | 3 => decide +kernel
  | 4 => decide +kernel
  | 5 => decide +kernel
  | 6 => decide +kernel
  | 7 => decide +kernel
  | 8 => decide +kernel
  | 9 => decide +kernel
  | 10 => decide +kernel
  | n + 11 => exact Nat.le_refl 0

def routes : Table Route :=
(.branch 1714
 (.branch 857
 (.branch 428
 (.branch 214
 (.branch 107
 (.branch 53
 (.branch 26
 (.branch 13
 (.leaf (.quota 1))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 39
 (.leaf (.quota 1))
 (.branch 46
 (.leaf (.quota 1))
 (.branch 49
 (.branch 47
 (.leaf (.quota 1))
 (.branch 48
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))))
 (.branch 80
 (.branch 66
 (.branch 59
 (.branch 56
 (.branch 54
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 62
 (.branch 60
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 64
 (.branch 63
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 65
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 73
 (.branch 69
 (.branch 67
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 93
 (.branch 86
 (.branch 83
 (.branch 81
 (.leaf (.quota 1))
 (.branch 82
 (.leaf (.reuse 8))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 160
 (.branch 133
 (.branch 120
 (.branch 113
 (.leaf (.quota 1))
 (.branch 116
 (.leaf (.quota 1))
 (.branch 118
 (.leaf (.quota 1))
 (.branch 119
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 126
 (.leaf (.quota 1))
 (.branch 129
 (.leaf (.quota 1))
 (.branch 131
 (.leaf (.quota 1))
 (.branch 132
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 146
 (.branch 139
 (.branch 136
 (.leaf (.quota 1))
 (.branch 137
 (.leaf (.quota 1))
 (.branch 138
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 142
 (.branch 140
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 153
 (.leaf (.quota 1))
 (.branch 156
 (.leaf (.quota 1))
 (.branch 158
 (.leaf (.quota 1))
 (.branch 159
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 187
 (.branch 173
 (.leaf (.quota 1))
 (.branch 180
 (.branch 176
 (.branch 174
 (.leaf (.quota 1))
 (.branch 175
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 178
 (.branch 177
 (.leaf (.reuse 15))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 200
 (.leaf (.quota 1))
 (.branch 207
 (.branch 203
 (.branch 201
 (.leaf (.quota 1))
 (.branch 202
 (.leaf (.reuse 16))
 (.leaf (.reuse 17))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 321
 (.branch 267
 (.branch 240
 (.branch 227
 (.branch 220
 (.branch 217
 (.branch 215
 (.leaf (.reuse 18))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 223
 (.leaf (.quota 1))
 (.branch 225
 (.leaf (.quota 1))
 (.branch 226
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 233
 (.leaf (.quota 1))
 (.branch 236
 (.leaf (.quota 1))
 (.branch 238
 (.leaf (.quota 1))
 (.branch 239
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 253
 (.branch 246
 (.branch 243
 (.leaf (.quota 1))
 (.branch 244
 (.leaf (.quota 1))
 (.branch 245
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 249
 (.branch 247
 (.leaf (.quota 1))
 (.branch 248
 (.leaf (.quota 1))
 (.leaf (.reuse 22))))
 (.leaf (.quota 1))))
 (.branch 260
 (.branch 256
 (.leaf (.quota 1))
 (.branch 258
 (.branch 257
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 263
 (.branch 261
 (.leaf (.quota 1))
 (.branch 262
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))))
 (.branch 294
 (.branch 280
 (.leaf (.quota 1))
 (.branch 287
 (.branch 283
 (.leaf (.quota 1))
 (.branch 285
 (.leaf (.quota 1))
 (.branch 286
 (.leaf (.quota 1))
 (.leaf (.reuse 25)))))
 (.branch 290
 (.leaf (.quota 1))
 (.branch 292
 (.branch 291
 (.leaf (.reuse 26))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 307
 (.branch 300
 (.leaf (.quota 1))
 (.branch 303
 (.branch 301
 (.leaf (.reuse 27))
 (.leaf (.quota 1)))
 (.branch 305
 (.leaf (.quota 1))
 (.branch 306
 (.leaf (.quota 1))
 (.leaf (.reuse 28))))))
 (.branch 314
 (.leaf (.quota 1))
 (.branch 317
 (.branch 315
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 319
 (.branch 318
 (.leaf (.reuse 30))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))
 (.branch 374
 (.branch 347
 (.branch 334
 (.branch 327
 (.branch 324
 (.branch 322
 (.leaf (.quota 1))
 (.branch 323
 (.leaf (.reuse 31))
 (.leaf (.quota 1))))
 (.branch 325
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 330
 (.branch 328
 (.leaf (.quota 1))
 (.branch 329
 (.leaf (.reuse 33))
 (.leaf (.quota 1))))
 (.branch 332
 (.branch 331
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 340
 (.branch 337
 (.branch 335
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 360
 (.branch 353
 (.branch 350
 (.branch 348
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 351
 (.leaf (.quota 1))
 (.branch 352
 (.leaf (.reuse 37))
 (.leaf (.quota 1)))))
 (.branch 356
 (.branch 354
 (.leaf (.quota 1))
 (.branch 355
 (.leaf (.quota 1))
 (.leaf (.reuse 38))))
 (.branch 358
 (.leaf (.quota 1))
 (.branch 359
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 367
 (.branch 363
 (.branch 361
 (.leaf (.quota 1))
 (.branch 362
 (.leaf (.quota 1))
 (.leaf (.reuse 40))))
 (.leaf (.quota 1)))
 (.branch 370
 (.branch 368
 (.leaf (.quota 2))
 (.branch 369
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))))
 (.branch 401
 (.branch 387
 (.branch 380
 (.leaf (.quota 1))
 (.branch 383
 (.leaf (.quota 1))
 (.branch 385
 (.leaf (.quota 1))
 (.branch 386
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 394
 (.branch 390
 (.leaf (.quota 1))
 (.branch 392
 (.leaf (.quota 1))
 (.branch 393
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 397
 (.branch 395
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))))
 (.branch 642
 (.branch 535
 (.branch 481
 (.branch 454
 (.branch 441
 (.branch 434
 (.branch 431
 (.branch 429
 (.leaf (.quota 2))
 (.branch 430
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 432
 (.leaf (.quota 1))
 (.branch 433
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 437
 (.branch 435
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 467
 (.leaf (.quota 1))
 (.branch 474
 (.leaf (.quota 1))
 (.branch 477
 (.leaf (.quota 1))
 (.branch 479
 (.branch 478
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))))
 (.branch 508
 (.branch 494
 (.branch 487
 (.branch 484
 (.leaf (.quota 1))
 (.branch 485
 (.leaf (.quota 1))
 (.branch 486
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1)))
 (.branch 501
 (.branch 497
 (.branch 495
 (.leaf (.quota 1))
 (.branch 496
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 521
 (.branch 514
 (.branch 511
 (.branch 509
 (.leaf (.quota 1))
 (.branch 510
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 588
 (.branch 561
 (.branch 548
 (.branch 541
 (.branch 538
 (.branch 536
 (.leaf (.quota 2))
 (.branch 537
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 544
 (.branch 542
 (.leaf (.quota 1))
 (.branch 543
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 546
 (.branch 545
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 554
 (.branch 551
 (.branch 549
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 574
 (.leaf (.quota 1))
 (.branch 581
 (.leaf (.quota 1))
 (.branch 584
 (.branch 582
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 615
 (.branch 601
 (.branch 594
 (.branch 591
 (.branch 589
 (.leaf (.quota 1))
 (.branch 590
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 597
 (.leaf (.quota 1))
 (.branch 599
 (.leaf (.quota 1))
 (.branch 600
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 608
 (.branch 604
 (.leaf (.quota 1))
 (.branch 606
 (.leaf (.quota 1))
 (.branch 607
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 611
 (.branch 609
 (.leaf (.quota 2))
 (.branch 610
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 613
 (.branch 612
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))
 (.branch 628
 (.branch 621
 (.branch 618
 (.branch 616
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 624
 (.leaf (.quota 1))
 (.branch 626
 (.leaf (.quota 1))
 (.branch 627
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 635
 (.branch 631
 (.branch 629
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 638
 (.branch 636
 (.leaf (.reuse 71))
 (.leaf (.quota 1)))
 (.branch 640
 (.branch 639
 (.leaf (.reuse 72))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))))
 (.branch 749
 (.branch 695
 (.branch 668
 (.branch 655
 (.branch 648
 (.branch 645
 (.branch 643
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 661
 (.leaf (.quota 1))
 (.branch 664
 (.leaf (.quota 1))
 (.branch 666
 (.leaf (.quota 1))
 (.branch 667
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 681
 (.branch 674
 (.branch 671
 (.leaf (.quota 1))
 (.branch 672
 (.leaf (.quota 1))
 (.branch 673
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 688
 (.branch 684
 (.branch 682
 (.leaf (.quota 1))
 (.branch 683
 (.leaf (.quota 1))
 (.leaf (.reuse 77))))
 (.branch 686
 (.branch 685
 (.leaf (.reuse 78))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 691
 (.branch 689
 (.leaf (.quota 1))
 (.branch 690
 (.leaf (.reuse 79))
 (.leaf (.reuse 80))))
 (.leaf (.quota 1))))))
 (.branch 722
 (.branch 708
 (.branch 701
 (.branch 698
 (.branch 696
 (.leaf (.quota 1))
 (.branch 697
 (.leaf (.quota 2))
 (.leaf (.reuse 82))))
 (.leaf (.quota 1)))
 (.branch 704
 (.leaf (.quota 1))
 (.branch 706
 (.branch 705
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 715
 (.branch 711
 (.leaf (.quota 1))
 (.branch 713
 (.branch 712
 (.leaf (.quota 1))
 (.leaf (.reuse 84)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 735
 (.branch 728
 (.branch 725
 (.branch 723
 (.leaf (.quota 1))
 (.branch 724
 (.leaf (.quota 1))
 (.leaf (.reuse 85))))
 (.branch 726
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 742
 (.leaf (.quota 1))
 (.branch 745
 (.leaf (.quota 1))
 (.branch 747
 (.leaf (.quota 1))
 (.branch 748
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 803
 (.branch 776
 (.branch 762
 (.leaf (.quota 1))
 (.branch 769
 (.branch 765
 (.branch 763
 (.leaf (.quota 2))
 (.branch 764
 (.leaf (.reuse 90))
 (.leaf (.quota 1))))
 (.branch 767
 (.leaf (.quota 1))
 (.branch 768
 (.leaf (.reuse 91))
 (.leaf (.reuse 92)))))
 (.branch 772
 (.branch 770
 (.leaf (.reuse 93))
 (.branch 771
 (.leaf (.reuse 94))
 (.leaf (.reuse 95))))
 (.leaf (.quota 1)))))
 (.branch 789
 (.branch 782
 (.leaf (.quota 1))
 (.branch 785
 (.branch 783
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 796
 (.leaf (.quota 1))
 (.branch 799
 (.branch 797
 (.leaf (.quota 1))
 (.branch 798
 (.leaf (.quota 1))
 (.leaf (.reuse 97))))
 (.leaf (.quota 1))))))
 (.branch 830
 (.branch 816
 (.branch 809
 (.branch 806
 (.branch 804
 (.leaf (.quota 1))
 (.branch 805
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 823
 (.branch 819
 (.leaf (.quota 1))
 (.branch 821
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 826
 (.branch 824
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 828
 (.leaf (.quota 1))
 (.branch 829
 (.leaf (.quota 1))
 (.leaf (.reuse 102)))))))
 (.branch 843
 (.branch 836
 (.leaf (.quota 1))
 (.branch 839
 (.leaf (.quota 1))
 (.branch 841
 (.branch 840
 (.leaf (.quota 1))
 (.leaf (.reuse 105)))
 (.branch 842
 (.leaf (.reuse 106))
 (.leaf (.reuse 107))))))
 (.branch 850
 (.branch 846
 (.branch 844
 (.leaf (.reuse 108))
 (.leaf (.quota 1)))
 (.branch 848
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 853
 (.branch 851
 (.leaf (.quota 2))
 (.branch 852
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))))))
 (.branch 1285
 (.branch 1071
 (.branch 964
 (.branch 910
 (.branch 883
 (.branch 870
 (.branch 863
 (.leaf (.quota 1))
 (.branch 866
 (.branch 864
 (.leaf (.reuse 115))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 876
 (.leaf (.quota 1))
 (.branch 879
 (.branch 877
 (.leaf (.quota 1))
 (.branch 878
 (.leaf (.reuse 118))
 (.leaf (.reuse 119))))
 (.leaf (.quota 1)))))
 (.branch 896
 (.leaf (.quota 1))
 (.branch 903
 (.branch 899
 (.branch 897
 (.leaf (.quota 2))
 (.branch 898
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 937
 (.branch 923
 (.branch 916
 (.branch 913
 (.branch 911
 (.leaf (.quota 1))
 (.branch 912
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 914
 (.leaf (.quota 1))
 (.branch 915
 (.leaf (.quota 1))
 (.leaf (.reuse 124)))))
 (.branch 919
 (.leaf (.quota 1))
 (.branch 921
 (.leaf (.quota 1))
 (.branch 922
 (.leaf (.reuse 125))
 (.leaf (.quota 1))))))
 (.branch 930
 (.leaf (.quota 1))
 (.branch 933
 (.leaf (.quota 1))
 (.branch 935
 (.leaf (.quota 1))
 (.branch 936
 (.leaf (.quota 2))
 (.leaf (.reuse 127)))))))
 (.branch 950
 (.branch 943
 (.branch 940
 (.branch 938
 (.leaf (.reuse 128))
 (.branch 939
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 941
 (.leaf (.reuse 130))
 (.branch 942
 (.leaf (.reuse 131))
 (.leaf (.quota 2)))))
 (.branch 946
 (.branch 944
 (.leaf (.quota 1))
 (.branch 945
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 948
 (.branch 947
 (.leaf (.quota 1))
 (.leaf (.reuse 135)))
 (.branch 949
 (.leaf (.reuse 136))
 (.leaf (.quota 1))))))
 (.branch 957
 (.branch 953
 (.branch 951
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 955
 (.leaf (.quota 1))
 (.branch 956
 (.leaf (.quota 1))
 (.leaf (.reuse 139)))))
 (.branch 960
 (.leaf (.quota 1))
 (.branch 962
 (.branch 961
 (.leaf (.reuse 142))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))
 (.branch 1017
 (.branch 990
 (.branch 977
 (.branch 970
 (.branch 967
 (.branch 965
 (.leaf (.reuse 143))
 (.leaf (.quota 1)))
 (.branch 968
 (.leaf (.quota 1))
 (.branch 969
 (.leaf (.reuse 144))
 (.leaf (.quota 1)))))
 (.branch 973
 (.branch 971
 (.leaf (.quota 1))
 (.branch 972
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 983
 (.branch 980
 (.leaf (.quota 1))
 (.branch 981
 (.leaf (.reuse 146))
 (.branch 982
 (.leaf (.quota 1))
 (.leaf (.reuse 147)))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1044
 (.branch 1030
 (.branch 1023
 (.branch 1020
 (.branch 1018
 (.leaf (.quota 1))
 (.branch 1019
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1026
 (.branch 1024
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1028
 (.branch 1027
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 1057
 (.branch 1050
 (.branch 1047
 (.leaf (.quota 1))
 (.branch 1048
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1053
 (.branch 1051
 (.leaf (.reuse 156))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 1178
 (.branch 1124
 (.branch 1097
 (.branch 1084
 (.leaf (.quota 1))
 (.branch 1090
 (.branch 1087
 (.branch 1085
 (.leaf (.reuse 157))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1110
 (.leaf (.quota 1))
 (.branch 1117
 (.branch 1113
 (.leaf (.quota 1))
 (.branch 1115
 (.leaf (.quota 1))
 (.branch 1116
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1120
 (.branch 1118
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1151
 (.branch 1137
 (.branch 1130
 (.leaf (.quota 1))
 (.branch 1133
 (.branch 1131
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1144
 (.branch 1140
 (.leaf (.quota 1))
 (.branch 1142
 (.branch 1141
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1147
 (.branch 1145
 (.leaf (.quota 2))
 (.branch 1146
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1149
 (.leaf (.quota 1))
 (.branch 1150
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 1164
 (.branch 1157
 (.leaf (.quota 1))
 (.branch 1160
 (.leaf (.quota 1))
 (.branch 1162
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1171
 (.branch 1167
 (.branch 1165
 (.leaf (.quota 2))
 (.branch 1166
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1231
 (.branch 1204
 (.branch 1191
 (.leaf (.quota 1))
 (.branch 1197
 (.branch 1194
 (.leaf (.quota 1))
 (.branch 1195
 (.leaf (.quota 2))
 (.branch 1196
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1200
 (.leaf (.quota 1))
 (.branch 1202
 (.branch 1201
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1203
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1217
 (.branch 1210
 (.leaf (.quota 1))
 (.branch 1213
 (.leaf (.quota 1))
 (.branch 1215
 (.branch 1214
 (.leaf (.reuse 178))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1224
 (.branch 1220
 (.branch 1218
 (.leaf (.quota 1))
 (.branch 1219
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1222
 (.leaf (.quota 1))
 (.branch 1223
 (.leaf (.reuse 182))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 1258
 (.branch 1244
 (.branch 1237
 (.leaf (.quota 1))
 (.branch 1240
 (.branch 1238
 (.leaf (.quota 1))
 (.branch 1239
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1242
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1251
 (.branch 1247
 (.branch 1245
 (.leaf (.quota 2))
 (.branch 1246
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1249
 (.leaf (.quota 1))
 (.branch 1250
 (.leaf (.reuse 189))
 (.leaf (.quota 1)))))
 (.branch 1254
 (.leaf (.quota 1))
 (.branch 1256
 (.leaf (.quota 1))
 (.branch 1257
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 1271
 (.branch 1264
 (.branch 1261
 (.leaf (.quota 1))
 (.branch 1262
 (.leaf (.quota 1))
 (.branch 1263
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1267
 (.branch 1265
 (.leaf (.reuse 192))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1278
 (.branch 1274
 (.leaf (.quota 1))
 (.branch 1276
 (.branch 1275
 (.leaf (.quota 1))
 (.leaf (.reuse 193)))
 (.leaf (.quota 1))))
 (.branch 1281
 (.branch 1279
 (.leaf (.quota 1))
 (.branch 1280
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))))
 (.branch 1499
 (.branch 1392
 (.branch 1338
 (.branch 1311
 (.branch 1298
 (.branch 1291
 (.branch 1288
 (.branch 1286
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1294
 (.branch 1292
 (.leaf (.quota 1))
 (.branch 1293
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1296
 (.leaf (.quota 2))
 (.branch 1297
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))
 (.branch 1324
 (.branch 1317
 (.branch 1314
 (.branch 1312
 (.leaf (.reuse 203))
 (.branch 1313
 (.leaf (.reuse 204))
 (.leaf (.reuse 205))))
 (.branch 1315
 (.leaf (.reuse 206))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1331
 (.branch 1327
 (.branch 1325
 (.leaf (.quota 1))
 (.branch 1326
 (.leaf (.reuse 209))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1365
 (.branch 1351
 (.branch 1344
 (.branch 1341
 (.branch 1339
 (.leaf (.quota 1))
 (.branch 1340
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1347
 (.branch 1345
 (.leaf (.reuse 211))
 (.leaf (.quota 1)))
 (.branch 1349
 (.branch 1348
 (.leaf (.quota 1))
 (.leaf (.reuse 212)))
 (.leaf (.quota 1)))))
 (.branch 1358
 (.branch 1354
 (.branch 1352
 (.leaf (.quota 1))
 (.branch 1353
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 1361
 (.branch 1359
 (.leaf (.quota 1))
 (.branch 1360
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1363
 (.branch 1362
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))
 (.branch 1378
 (.branch 1371
 (.branch 1368
 (.branch 1366
 (.leaf (.quota 1))
 (.branch 1367
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1374
 (.leaf (.quota 1))
 (.branch 1376
 (.branch 1375
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1385
 (.branch 1381
 (.branch 1379
 (.leaf (.quota 2))
 (.branch 1380
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1388
 (.branch 1386
 (.leaf (.quota 2))
 (.branch 1387
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))
 (.branch 1445
 (.branch 1418
 (.branch 1405
 (.branch 1398
 (.leaf (.quota 1))
 (.branch 1401
 (.branch 1399
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1403
 (.leaf (.quota 1))
 (.branch 1404
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1411
 (.leaf (.quota 1))
 (.branch 1414
 (.leaf (.quota 1))
 (.branch 1416
 (.branch 1415
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1417
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 1431
 (.branch 1424
 (.branch 1421
 (.branch 1419
 (.leaf (.quota 2))
 (.branch 1420
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 1427
 (.branch 1425
 (.leaf (.quota 1))
 (.branch 1426
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1429
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1438
 (.branch 1434
 (.branch 1432
 (.leaf (.quota 1))
 (.branch 1433
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1436
 (.leaf (.quota 1))
 (.branch 1437
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1441
 (.leaf (.quota 1))
 (.branch 1443
 (.branch 1442
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 1472
 (.branch 1458
 (.branch 1451
 (.leaf (.quota 1))
 (.branch 1454
 (.branch 1452
 (.leaf (.quota 1))
 (.branch 1453
 (.leaf (.reuse 237))
 (.leaf (.quota 1))))
 (.branch 1456
 (.branch 1455
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 1465
 (.branch 1461
 (.branch 1459
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1468
 (.branch 1466
 (.leaf (.quota 1))
 (.branch 1467
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1470
 (.branch 1469
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))))
 (.branch 1606
 (.branch 1552
 (.branch 1525
 (.branch 1512
 (.leaf (.quota 1))
 (.branch 1518
 (.branch 1515
 (.branch 1513
 (.leaf (.quota 1))
 (.branch 1514
 (.leaf (.reuse 244))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1538
 (.branch 1531
 (.leaf (.quota 1))
 (.branch 1534
 (.branch 1532
 (.leaf (.quota 1))
 (.branch 1533
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1536
 (.branch 1535
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 1545
 (.leaf (.quota 1))
 (.branch 1548
 (.leaf (.quota 1))
 (.branch 1550
 (.branch 1549
 (.leaf (.reuse 248))
 (.leaf (.quota 1)))
 (.branch 1551
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 1579
 (.branch 1565
 (.branch 1558
 (.branch 1555
 (.leaf (.quota 1))
 (.branch 1556
 (.leaf (.quota 1))
 (.branch 1557
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1561
 (.branch 1559
 (.leaf (.quota 1))
 (.branch 1560
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1563
 (.branch 1562
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1564
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))
 (.branch 1592
 (.leaf (.quota 1))
 (.branch 1599
 (.leaf (.quota 1))
 (.branch 1602
 (.leaf (.quota 1))
 (.branch 1604
 (.branch 1603
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))))
 (.branch 1660
 (.branch 1633
 (.branch 1619
 (.branch 1612
 (.leaf (.quota 1))
 (.branch 1615
 (.branch 1613
 (.leaf (.quota 1))
 (.branch 1614
 (.leaf (.quota 1))
 (.leaf (.reuse 257))))
 (.branch 1617
 (.branch 1616
 (.leaf (.reuse 258))
 (.leaf (.reuse 259)))
 (.leaf (.quota 1)))))
 (.branch 1626
 (.branch 1622
 (.leaf (.quota 1))
 (.branch 1624
 (.leaf (.quota 1))
 (.branch 1625
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1629
 (.branch 1627
 (.leaf (.quota 1))
 (.branch 1628
 (.leaf (.reuse 262))
 (.leaf (.quota 1))))
 (.branch 1631
 (.leaf (.quota 1))
 (.branch 1632
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1646
 (.branch 1639
 (.leaf (.quota 1))
 (.branch 1642
 (.branch 1640
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 1687
 (.branch 1673
 (.branch 1666
 (.branch 1663
 (.leaf (.quota 1))
 (.branch 1664
 (.leaf (.quota 1))
 (.branch 1665
 (.leaf (.reuse 269))
 (.leaf (.quota 1)))))
 (.branch 1669
 (.branch 1667
 (.leaf (.reuse 270))
 (.leaf (.quota 1)))
 (.branch 1671
 (.branch 1670
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 1680
 (.branch 1676
 (.leaf (.quota 1))
 (.branch 1678
 (.leaf (.quota 1))
 (.branch 1679
 (.leaf (.quota 1))
 (.leaf (.reuse 272)))))
 (.branch 1683
 (.branch 1681
 (.leaf (.reuse 273))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1700
 (.branch 1693
 (.leaf (.quota 1))
 (.branch 1696
 (.branch 1694
 (.leaf (.reuse 276))
 (.branch 1695
 (.leaf (.reuse 277))
 (.leaf (.reuse 278))))
 (.branch 1698
 (.branch 1697
 (.leaf (.reuse 279))
 (.leaf (.quota 1)))
 (.branch 1699
 (.leaf (.quota 1))
 (.leaf (.reuse 281))))))
 (.branch 1707
 (.branch 1703
 (.branch 1701
 (.leaf (.quota 1))
 (.branch 1702
 (.leaf (.reuse 282))
 (.leaf (.quota 1))))
 (.branch 1705
 (.leaf (.quota 1))
 (.branch 1706
 (.leaf (.quota 1))
 (.leaf (.reuse 283)))))
 (.branch 1710
 (.leaf (.quota 1))
 (.branch 1712
 (.branch 1711
 (.leaf (.reuse 285))
 (.leaf (.reuse 286)))
 (.leaf (.quota 1))))))))))))
 (.branch 2571
 (.branch 2142
 (.branch 1928
 (.branch 1821
 (.branch 1767
 (.branch 1740
 (.branch 1727
 (.branch 1720
 (.branch 1717
 (.leaf (.quota 1))
 (.branch 1718
 (.leaf (.quota 1))
 (.branch 1719
 (.leaf (.reuse 288))
 (.leaf (.reuse 289)))))
 (.branch 1723
 (.branch 1721
 (.leaf (.reuse 290))
 (.branch 1722
 (.leaf (.reuse 291))
 (.leaf (.quota 2))))
 (.branch 1725
 (.branch 1724
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1733
 (.branch 1730
 (.leaf (.quota 1))
 (.branch 1731
 (.leaf (.reuse 295))
 (.leaf (.quota 1))))
 (.branch 1736
 (.leaf (.quota 1))
 (.branch 1738
 (.branch 1737
 (.leaf (.reuse 297))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1753
 (.branch 1746
 (.branch 1743
 (.branch 1741
 (.leaf (.reuse 298))
 (.leaf (.quota 1)))
 (.branch 1744
 (.leaf (.quota 1))
 (.branch 1745
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1749
 (.branch 1747
 (.leaf (.quota 1))
 (.branch 1748
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 1760
 (.branch 1756
 (.branch 1754
 (.leaf (.quota 1))
 (.branch 1755
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1758
 (.branch 1757
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 1763
 (.leaf (.quota 1))
 (.branch 1765
 (.branch 1764
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 1794
 (.branch 1780
 (.branch 1773
 (.branch 1770
 (.branch 1768
 (.leaf (.quota 1))
 (.branch 1769
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1787
 (.leaf (.quota 1))
 (.branch 1790
 (.leaf (.quota 1))
 (.branch 1792
 (.leaf (.quota 1))
 (.branch 1793
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 1807
 (.branch 1800
 (.branch 1797
 (.leaf (.quota 1))
 (.branch 1798
 (.leaf (.quota 2))
 (.branch 1799
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1803
 (.branch 1801
 (.leaf (.quota 1))
 (.branch 1802
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1805
 (.leaf (.quota 1))
 (.branch 1806
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1814
 (.branch 1810
 (.branch 1808
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1812
 (.leaf (.quota 1))
 (.branch 1813
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1))))))
 (.branch 1874
 (.branch 1847
 (.branch 1834
 (.leaf (.quota 1))
 (.branch 1840
 (.branch 1837
 (.branch 1835
 (.leaf (.quota 2))
 (.branch 1836
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1843
 (.leaf (.quota 1))
 (.branch 1845
 (.branch 1844
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1860
 (.branch 1853
 (.branch 1850
 (.branch 1848
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1851
 (.leaf (.quota 1))
 (.branch 1852
 (.leaf (.quota 1))
 (.leaf (.reuse 317)))))
 (.branch 1856
 (.leaf (.quota 1))
 (.branch 1858
 (.branch 1857
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1867
 (.branch 1863
 (.branch 1861
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1865
 (.branch 1864
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1866
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1870
 (.leaf (.quota 1))
 (.branch 1872
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 1901
 (.branch 1887
 (.branch 1880
 (.branch 1877
 (.leaf (.quota 1))
 (.branch 1878
 (.leaf (.quota 1))
 (.branch 1879
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1883
 (.leaf (.quota 1))
 (.branch 1885
 (.branch 1884
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1886
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1894
 (.branch 1890
 (.branch 1888
 (.leaf (.reuse 329))
 (.leaf (.quota 1)))
 (.branch 1892
 (.leaf (.quota 2))
 (.branch 1893
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1897
 (.branch 1895
 (.leaf (.quota 1))
 (.branch 1896
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))
 (.branch 1914
 (.branch 1907
 (.branch 1904
 (.leaf (.quota 1))
 (.branch 1905
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1910
 (.branch 1908
 (.leaf (.quota 1))
 (.branch 1909
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1912
 (.branch 1911
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1913
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1921
 (.branch 1917
 (.leaf (.quota 1))
 (.branch 1919
 (.branch 1918
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1920
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1924
 (.branch 1922
 (.leaf (.quota 1))
 (.branch 1923
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1926
 (.branch 1925
 (.leaf (.quota 1))
 (.leaf (.reuse 341)))
 (.leaf (.quota 1)))))))))
 (.branch 2035
 (.branch 1981
 (.branch 1954
 (.branch 1941
 (.branch 1934
 (.branch 1931
 (.branch 1929
 (.leaf (.reuse 342))
 (.leaf (.quota 1)))
 (.branch 1932
 (.leaf (.quota 1))
 (.branch 1933
 (.leaf (.reuse 343))
 (.leaf (.reuse 344)))))
 (.leaf (.quota 1)))
 (.branch 1947
 (.leaf (.quota 1))
 (.branch 1950
 (.branch 1948
 (.leaf (.quota 1))
 (.branch 1949
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1952
 (.branch 1951
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1967
 (.branch 1960
 (.branch 1957
 (.leaf (.quota 1))
 (.branch 1958
 (.leaf (.quota 1))
 (.branch 1959
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1963
 (.leaf (.quota 1))
 (.branch 1965
 (.branch 1964
 (.leaf (.reuse 350))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1974
 (.branch 1970
 (.branch 1968
 (.leaf (.quota 1))
 (.branch 1969
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2008
 (.branch 1994
 (.branch 1987
 (.branch 1984
 (.branch 1982
 (.leaf (.quota 1))
 (.branch 1983
 (.leaf (.reuse 353))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1990
 (.branch 1988
 (.leaf (.quota 1))
 (.branch 1989
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1992
 (.leaf (.quota 1))
 (.branch 1993
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2001
 (.branch 1997
 (.branch 1995
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2004
 (.leaf (.quota 1))
 (.branch 2006
 (.leaf (.quota 1))
 (.branch 2007
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2021
 (.branch 2014
 (.branch 2011
 (.leaf (.quota 1))
 (.branch 2012
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2017
 (.leaf (.quota 1))
 (.branch 2019
 (.leaf (.quota 1))
 (.branch 2020
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2028
 (.branch 2024
 (.leaf (.quota 1))
 (.branch 2026
 (.leaf (.quota 1))
 (.branch 2027
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2031
 (.leaf (.quota 1))
 (.branch 2033
 (.leaf (.quota 1))
 (.branch 2034
 (.leaf (.reuse 364))
 (.leaf (.quota 1)))))))))
 (.branch 2088
 (.leaf (.quota 1))
 (.branch 2115
 (.leaf (.quota 1))
 (.branch 2128
 (.leaf (.quota 1))
 (.branch 2135
 (.branch 2131
 (.branch 2129
 (.leaf (.quota 1))
 (.branch 2130
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))
 (.branch 2356
 (.branch 2249
 (.branch 2195
 (.branch 2168
 (.branch 2155
 (.branch 2148
 (.branch 2145
 (.leaf (.quota 1))
 (.branch 2146
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2161
 (.branch 2158
 (.leaf (.quota 1))
 (.branch 2159
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 2181
 (.branch 2174
 (.leaf (.quota 1))
 (.branch 2177
 (.branch 2175
 (.leaf (.quota 1))
 (.branch 2176
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2179
 (.leaf (.quota 1))
 (.branch 2180
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2188
 (.branch 2184
 (.branch 2182
 (.leaf (.quota 2))
 (.branch 2183
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2186
 (.leaf (.quota 1))
 (.branch 2187
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2191
 (.leaf (.quota 1))
 (.branch 2193
 (.leaf (.quota 2))
 (.branch 2194
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 2222
 (.branch 2208
 (.branch 2201
 (.branch 2198
 (.branch 2196
 (.leaf (.quota 1))
 (.branch 2197
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2215
 (.branch 2211
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2218
 (.branch 2216
 (.leaf (.quota 2))
 (.branch 2217
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 2235
 (.leaf (.quota 1))
 (.branch 2242
 (.leaf (.quota 1))
 (.branch 2245
 (.branch 2243
 (.leaf (.quota 1))
 (.branch 2244
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))
 (.branch 2302
 (.branch 2275
 (.branch 2262
 (.branch 2255
 (.branch 2252
 (.leaf (.quota 1))
 (.branch 2253
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2288
 (.branch 2281
 (.leaf (.quota 1))
 (.branch 2284
 (.branch 2282
 (.leaf (.quota 2))
 (.branch 2283
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 2295
 (.leaf (.quota 1))
 (.branch 2298
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2329
 (.branch 2315
 (.branch 2308
 (.leaf (.quota 1))
 (.branch 2311
 (.leaf (.quota 1))
 (.branch 2313
 (.branch 2312
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2314
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2322
 (.branch 2318
 (.leaf (.quota 1))
 (.branch 2320
 (.branch 2319
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2325
 (.leaf (.quota 1))
 (.branch 2327
 (.branch 2326
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 2342
 (.branch 2335
 (.branch 2332
 (.branch 2330
 (.leaf (.quota 2))
 (.branch 2331
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2338
 (.branch 2336
 (.leaf (.quota 1))
 (.branch 2337
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2340
 (.leaf (.quota 1))
 (.branch 2341
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2349
 (.branch 2345
 (.leaf (.quota 1))
 (.branch 2347
 (.branch 2346
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))
 (.branch 2463
 (.branch 2409
 (.branch 2382
 (.branch 2369
 (.branch 2362
 (.branch 2359
 (.leaf (.quota 1))
 (.branch 2360
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2395
 (.branch 2388
 (.branch 2385
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2402
 (.leaf (.quota 1))
 (.branch 2405
 (.branch 2403
 (.leaf (.quota 1))
 (.branch 2404
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2407
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2436
 (.branch 2422
 (.branch 2415
 (.branch 2412
 (.branch 2410
 (.leaf (.quota 2))
 (.branch 2411
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2413
 (.leaf (.quota 1))
 (.branch 2414
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2418
 (.leaf (.quota 1))
 (.branch 2420
 (.leaf (.quota 1))
 (.branch 2421
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2429
 (.branch 2425
 (.branch 2423
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2432
 (.branch 2430
 (.leaf (.quota 2))
 (.branch 2431
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2434
 (.leaf (.quota 1))
 (.branch 2435
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 2449
 (.leaf (.quota 1))
 (.branch 2456
 (.branch 2452
 (.branch 2450
 (.leaf (.quota 1))
 (.branch 2451
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2454
 (.branch 2453
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 2517
 (.branch 2490
 (.branch 2476
 (.branch 2469
 (.branch 2466
 (.branch 2464
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2467
 (.leaf (.quota 1))
 (.branch 2468
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2472
 (.leaf (.quota 1))
 (.branch 2474
 (.leaf (.quota 2))
 (.branch 2475
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2483
 (.branch 2479
 (.branch 2477
 (.leaf (.quota 2))
 (.branch 2478
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2481
 (.branch 2480
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 2486
 (.branch 2484
 (.leaf (.quota 2))
 (.branch 2485
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 2503
 (.branch 2496
 (.branch 2493
 (.leaf (.quota 1))
 (.branch 2494
 (.leaf (.quota 2))
 (.branch 2495
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2499
 (.branch 2497
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2501
 (.leaf (.quota 1))
 (.branch 2502
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2510
 (.branch 2506
 (.branch 2504
 (.leaf (.quota 2))
 (.branch 2505
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2544
 (.branch 2530
 (.branch 2523
 (.branch 2520
 (.branch 2518
 (.leaf (.quota 2))
 (.branch 2519
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2526
 (.branch 2524
 (.leaf (.quota 1))
 (.branch 2525
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2528
 (.branch 2527
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2537
 (.branch 2533
 (.leaf (.quota 1))
 (.branch 2535
 (.branch 2534
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 2540
 (.branch 2538
 (.leaf (.quota 1))
 (.branch 2539
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2542
 (.leaf (.quota 1))
 (.branch 2543
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2557
 (.branch 2550
 (.branch 2547
 (.branch 2545
 (.leaf (.quota 1))
 (.branch 2546
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2553
 (.branch 2551
 (.leaf (.quota 1))
 (.branch 2552
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 2564
 (.branch 2560
 (.leaf (.quota 1))
 (.branch 2562
 (.leaf (.quota 1))
 (.branch 2563
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1)))))))))
 (.branch 2999
 (.branch 2785
 (.branch 2678
 (.branch 2624
 (.branch 2597
 (.branch 2584
 (.branch 2577
 (.branch 2574
 (.leaf (.quota 1))
 (.branch 2575
 (.leaf (.quota 1))
 (.branch 2576
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2580
 (.leaf (.quota 1))
 (.branch 2582
 (.branch 2581
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 2590
 (.branch 2587
 (.leaf (.quota 1))
 (.branch 2588
 (.leaf (.quota 1))
 (.branch 2589
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2593
 (.branch 2591
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2595
 (.branch 2594
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2596
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2610
 (.branch 2603
 (.branch 2600
 (.branch 2598
 (.leaf (.quota 2))
 (.branch 2599
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2606
 (.branch 2604
 (.leaf (.quota 1))
 (.branch 2605
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2608
 (.branch 2607
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2617
 (.branch 2613
 (.branch 2611
 (.leaf (.quota 2))
 (.branch 2612
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2615
 (.leaf (.quota 1))
 (.branch 2616
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2620
 (.branch 2618
 (.leaf (.quota 1))
 (.branch 2619
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 2651
 (.branch 2637
 (.branch 2630
 (.branch 2627
 (.leaf (.quota 1))
 (.branch 2628
 (.leaf (.quota 2))
 (.branch 2629
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 2644
 (.branch 2640
 (.branch 2638
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2664
 (.branch 2657
 (.leaf (.quota 1))
 (.branch 2660
 (.leaf (.quota 1))
 (.branch 2662
 (.branch 2661
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2671
 (.branch 2667
 (.leaf (.quota 1))
 (.branch 2669
 (.branch 2668
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2674
 (.branch 2672
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2676
 (.leaf (.quota 1))
 (.branch 2677
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 2731
 (.branch 2704
 (.leaf (.quota 1))
 (.branch 2717
 (.branch 2710
 (.branch 2707
 (.branch 2705
 (.leaf (.quota 1))
 (.branch 2706
 (.leaf (.reuse 475))
 (.leaf (.quota 1))))
 (.branch 2708
 (.leaf (.reuse 476))
 (.branch 2709
 (.leaf (.reuse 477))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2758
 (.branch 2744
 (.branch 2737
 (.leaf (.quota 1))
 (.branch 2740
 (.leaf (.quota 1))
 (.branch 2742
 (.branch 2741
 (.leaf (.reuse 478))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2751
 (.branch 2747
 (.leaf (.quota 1))
 (.branch 2749
 (.leaf (.quota 1))
 (.branch 2750
 (.leaf (.reuse 479))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 2771
 (.branch 2764
 (.branch 2761
 (.branch 2759
 (.leaf (.quota 1))
 (.branch 2760
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 2767
 (.leaf (.quota 1))
 (.branch 2769
 (.branch 2768
 (.leaf (.quota 1))
 (.leaf (.reuse 481)))
 (.branch 2770
 (.leaf (.reuse 482))
 (.leaf (.quota 1))))))
 (.branch 2778
 (.branch 2774
 (.leaf (.quota 1))
 (.branch 2776
 (.branch 2775
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2781
 (.branch 2779
 (.leaf (.quota 1))
 (.branch 2780
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2783
 (.branch 2782
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))))
 (.branch 2892
 (.branch 2838
 (.branch 2811
 (.branch 2798
 (.branch 2791
 (.branch 2788
 (.branch 2786
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2789
 (.leaf (.quota 1))
 (.branch 2790
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2794
 (.branch 2792
 (.leaf (.quota 2))
 (.branch 2793
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2824
 (.branch 2817
 (.branch 2814
 (.branch 2812
 (.leaf (.quota 1))
 (.branch 2813
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2815
 (.leaf (.quota 1))
 (.branch 2816
 (.leaf (.quota 1))
 (.leaf (.reuse 491)))))
 (.leaf (.quota 1)))
 (.branch 2831
 (.branch 2827
 (.branch 2825
 (.leaf (.quota 1))
 (.branch 2826
 (.leaf (.reuse 494))
 (.leaf (.reuse 495))))
 (.branch 2829
 (.branch 2828
 (.leaf (.quota 1))
 (.leaf (.reuse 497)))
 (.leaf (.quota 1))))
 (.branch 2834
 (.leaf (.quota 1))
 (.branch 2836
 (.branch 2835
 (.leaf (.quota 1))
 (.leaf (.reuse 499)))
 (.branch 2837
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 2865
 (.branch 2851
 (.branch 2844
 (.branch 2841
 (.leaf (.quota 1))
 (.branch 2842
 (.leaf (.quota 1))
 (.branch 2843
 (.leaf (.reuse 501))
 (.leaf (.quota 1)))))
 (.branch 2847
 (.branch 2845
 (.leaf (.quota 1))
 (.branch 2846
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2849
 (.branch 2848
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 2858
 (.branch 2854
 (.branch 2852
 (.leaf (.quota 1))
 (.branch 2853
 (.leaf (.reuse 504))
 (.leaf (.quota 1))))
 (.branch 2856
 (.branch 2855
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 2861
 (.leaf (.quota 1))
 (.branch 2863
 (.leaf (.quota 1))
 (.branch 2864
 (.leaf (.quota 1))
 (.leaf (.reuse 506)))))))
 (.branch 2878
 (.branch 2871
 (.leaf (.quota 1))
 (.branch 2874
 (.leaf (.quota 1))
 (.branch 2876
 (.branch 2875
 (.leaf (.quota 1))
 (.leaf (.reuse 507)))
 (.leaf (.quota 1)))))
 (.branch 2885
 (.branch 2881
 (.leaf (.quota 1))
 (.branch 2883
 (.branch 2882
 (.leaf (.reuse 508))
 (.leaf (.reuse 509)))
 (.branch 2884
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))))
 (.branch 2945
 (.branch 2918
 (.branch 2905
 (.leaf (.quota 1))
 (.branch 2911
 (.branch 2908
 (.branch 2906
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2909
 (.leaf (.quota 1))
 (.branch 2910
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1))))
 (.branch 2931
 (.branch 2924
 (.branch 2921
 (.leaf (.quota 1))
 (.branch 2922
 (.leaf (.quota 1))
 (.branch 2923
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2927
 (.leaf (.quota 1))
 (.branch 2929
 (.branch 2928
 (.leaf (.reuse 514))
 (.leaf (.quota 1)))
 (.branch 2930
 (.leaf (.quota 2))
 (.leaf (.reuse 516))))))
 (.branch 2938
 (.branch 2934
 (.branch 2932
 (.leaf (.quota 1))
 (.branch 2933
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2941
 (.branch 2939
 (.leaf (.quota 2))
 (.branch 2940
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 2972
 (.branch 2958
 (.branch 2951
 (.branch 2948
 (.leaf (.quota 1))
 (.branch 2949
 (.leaf (.reuse 522))
 (.branch 2950
 (.leaf (.reuse 523))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 2965
 (.branch 2961
 (.branch 2959
 (.leaf (.reuse 525))
 (.branch 2960
 (.leaf (.reuse 526))
 (.leaf (.quota 1))))
 (.branch 2963
 (.branch 2962
 (.leaf (.quota 1))
 (.leaf (.reuse 528)))
 (.branch 2964
 (.leaf (.reuse 529))
 (.leaf (.quota 1)))))
 (.branch 2968
 (.branch 2966
 (.leaf (.quota 1))
 (.branch 2967
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2970
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2985
 (.branch 2978
 (.branch 2975
 (.leaf (.quota 1))
 (.branch 2976
 (.leaf (.quota 1))
 (.branch 2977
 (.leaf (.quota 1))
 (.leaf (.reuse 533)))))
 (.branch 2981
 (.leaf (.quota 1))
 (.branch 2983
 (.leaf (.quota 1))
 (.branch 2984
 (.leaf (.quota 2))
 (.leaf (.reuse 536))))))
 (.branch 2992
 (.branch 2988
 (.leaf (.quota 1))
 (.branch 2990
 (.leaf (.quota 1))
 (.branch 2991
 (.leaf (.quota 1))
 (.leaf (.reuse 537)))))
 (.branch 2995
 (.branch 2993
 (.leaf (.quota 1))
 (.branch 2994
 (.leaf (.quota 1))
 (.leaf (.reuse 539))))
 (.leaf (.quota 1)))))))))
 (.branch 3213
 (.branch 3106
 (.branch 3052
 (.branch 3025
 (.branch 3012
 (.branch 3005
 (.branch 3002
 (.leaf (.quota 1))
 (.branch 3003
 (.leaf (.quota 1))
 (.branch 3004
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1)))
 (.branch 3018
 (.branch 3015
 (.leaf (.quota 1))
 (.branch 3016
 (.leaf (.quota 1))
 (.branch 3017
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3021
 (.branch 3019
 (.leaf (.quota 2))
 (.branch 3020
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3023
 (.branch 3022
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 3038
 (.branch 3031
 (.branch 3028
 (.branch 3026
 (.leaf (.quota 1))
 (.branch 3027
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 3034
 (.leaf (.quota 1))
 (.branch 3036
 (.leaf (.quota 1))
 (.branch 3037
 (.leaf (.reuse 546))
 (.leaf (.reuse 547))))))
 (.leaf (.quota 1))))
 (.branch 3079
 (.branch 3065
 (.branch 3058
 (.branch 3055
 (.branch 3053
 (.leaf (.quota 1))
 (.branch 3054
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 3061
 (.leaf (.quota 1))
 (.branch 3063
 (.branch 3062
 (.leaf (.quota 1))
 (.leaf (.reuse 549)))
 (.branch 3064
 (.leaf (.reuse 550))
 (.leaf (.quota 1))))))
 (.branch 3072
 (.branch 3068
 (.branch 3066
 (.leaf (.quota 1))
 (.branch 3067
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3070
 (.branch 3069
 (.leaf (.quota 1))
 (.leaf (.reuse 552)))
 (.branch 3071
 (.leaf (.quota 1))
 (.leaf (.reuse 553)))))
 (.branch 3075
 (.leaf (.quota 1))
 (.branch 3077
 (.branch 3076
 (.leaf (.reuse 554))
 (.leaf (.quota 1)))
 (.branch 3078
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 3092
 (.leaf (.quota 1))
 (.branch 3099
 (.leaf (.quota 1))
 (.branch 3102
 (.branch 3100
 (.leaf (.quota 1))
 (.branch 3101
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3104
 (.branch 3103
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))))
 (.branch 3159
 (.branch 3132
 (.branch 3119
 (.branch 3112
 (.branch 3109
 (.branch 3107
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3115
 (.branch 3113
 (.leaf (.reuse 561))
 (.leaf (.quota 1)))
 (.branch 3117
 (.branch 3116
 (.leaf (.quota 1))
 (.leaf (.reuse 562)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3186
 (.branch 3172
 (.branch 3165
 (.branch 3162
 (.leaf (.quota 1))
 (.branch 3163
 (.leaf (.reuse 563))
 (.leaf (.quota 1))))
 (.branch 3168
 (.leaf (.quota 1))
 (.branch 3170
 (.branch 3169
 (.leaf (.quota 1))
 (.leaf (.reuse 564)))
 (.branch 3171
 (.leaf (.quota 1))
 (.leaf (.reuse 565))))))
 (.branch 3179
 (.branch 3175
 (.branch 3173
 (.leaf (.quota 1))
 (.branch 3174
 (.leaf (.quota 1))
 (.leaf (.reuse 566))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3199
 (.branch 3192
 (.leaf (.quota 1))
 (.branch 3195
 (.leaf (.quota 1))
 (.branch 3197
 (.leaf (.quota 1))
 (.branch 3198
 (.leaf (.quota 1))
 (.leaf (.reuse 567))))))
 (.branch 3206
 (.branch 3202
 (.leaf (.quota 1))
 (.branch 3204
 (.branch 3203
 (.leaf (.quota 1))
 (.leaf (.reuse 570)))
 (.leaf (.quota 1))))
 (.branch 3209
 (.leaf (.quota 1))
 (.branch 3211
 (.leaf (.quota 1))
 (.branch 3212
 (.leaf (.reuse 572))
 (.leaf (.quota 1))))))))))
 (.branch 3320
 (.branch 3266
 (.branch 3239
 (.branch 3226
 (.branch 3219
 (.branch 3216
 (.leaf (.quota 1))
 (.branch 3217
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3222
 (.branch 3220
 (.leaf (.quota 1))
 (.branch 3221
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3224
 (.branch 3223
 (.leaf (.reuse 576))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 3232
 (.branch 3229
 (.branch 3227
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3230
 (.leaf (.reuse 578))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 3252
 (.branch 3245
 (.branch 3242
 (.branch 3240
 (.leaf (.quota 1))
 (.branch 3241
 (.leaf (.quota 1))
 (.leaf (.reuse 579))))
 (.leaf (.quota 1)))
 (.branch 3248
 (.branch 3246
 (.leaf (.reuse 582))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3259
 (.branch 3255
 (.branch 3253
 (.leaf (.quota 1))
 (.branch 3254
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 3262
 (.branch 3260
 (.leaf (.quota 1))
 (.branch 3261
 (.leaf (.reuse 585))
 (.leaf (.quota 2))))
 (.branch 3264
 (.branch 3263
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 3293
 (.branch 3279
 (.branch 3272
 (.leaf (.quota 1))
 (.branch 3275
 (.leaf (.quota 1))
 (.branch 3277
 (.branch 3276
 (.leaf (.quota 1))
 (.leaf (.reuse 590)))
 (.leaf (.quota 1)))))
 (.branch 3286
 (.branch 3282
 (.leaf (.quota 1))
 (.branch 3284
 (.branch 3283
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3285
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3289
 (.leaf (.quota 1))
 (.branch 3291
 (.leaf (.quota 1))
 (.branch 3292
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 3306
 (.branch 3299
 (.branch 3296
 (.branch 3294
 (.leaf (.quota 2))
 (.branch 3295
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3313
 (.branch 3309
 (.branch 3307
 (.leaf (.quota 1))
 (.branch 3308
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3311
 (.branch 3310
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3312
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3316
 (.branch 3314
 (.leaf (.quota 1))
 (.branch 3315
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3318
 (.leaf (.quota 2))
 (.branch 3319
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 3374
 (.branch 3347
 (.branch 3333
 (.branch 3326
 (.branch 3323
 (.branch 3321
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3324
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 3340
 (.branch 3336
 (.leaf (.quota 1))
 (.branch 3338
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 3360
 (.leaf (.quota 1))
 (.branch 3367
 (.branch 3363
 (.leaf (.quota 1))
 (.branch 3365
 (.branch 3364
 (.leaf (.reuse 615))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3370
 (.branch 3368
 (.leaf (.quota 1))
 (.branch 3369
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3372
 (.branch 3371
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3373
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 3401
 (.branch 3387
 (.branch 3380
 (.branch 3377
 (.branch 3375
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 3383
 (.leaf (.quota 1))
 (.branch 3385
 (.branch 3384
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 3394
 (.branch 3390
 (.branch 3388
 (.leaf (.quota 1))
 (.branch 3389
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3392
 (.branch 3391
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3393
 (.leaf (.quota 1))
 (.leaf (.quota 3)))))
 (.branch 3397
 (.branch 3395
 (.leaf (.quota 1))
 (.branch 3396
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3399
 (.branch 3398
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))))
 (.branch 3414
 (.branch 3407
 (.branch 3404
 (.branch 3402
 (.leaf (.quota 1))
 (.branch 3403
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3405
 (.leaf (.quota 1))
 (.branch 3406
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3410
 (.branch 3408
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3412
 (.leaf (.quota 1))
 (.branch 3413
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3421
 (.branch 3417
 (.branch 3415
 (.leaf (.quota 1))
 (.branch 3416
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3419
 (.leaf (.quota 1))
 (.branch 3420
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3424
 (.leaf (.quota 2))
 (.branch 3426
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0722.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0722.rawLeaves 644 (RootedForests.RootedSubsumedForest0724.rawLeaves i) (routes.get i)

def disposition (j : Fin 3428) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0722.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0722

/- Original module: RootedQuotaTransfer0722Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_complete : Interval test0 0 128 :=
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 128
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 128
  test0_block_6
  test0_block_7)))
theorem routeInterval0 : Interval routeTest 0 128 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0722

/- Original module: RootedQuotaTransfer0722Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0722
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 32 :=
  interval_of_check test128 16 16 (by decide +kernel)

theorem test128_block_2 : Interval test128 32 48 :=
  interval_of_check test128 32 16 (by decide +kernel)

theorem test128_block_3 : Interval test128 48 64 :=
  interval_of_check test128 48 16 (by decide +kernel)

theorem test128_block_4 : Interval test128 64 80 :=
  interval_of_check test128 64 16 (by decide +kernel)

theorem test128_block_5 : Interval test128 80 96 :=
  interval_of_check test128 80 16 (by decide +kernel)

theorem test128_block_6 : Interval test128 96 112 :=
  interval_of_check test128 96 16 (by decide +kernel)

theorem test128_block_7 : Interval test128 112 128 :=
  interval_of_check test128 112 16 (by decide +kernel)

theorem test128_complete : Interval test128 0 128 :=
  (interval_append test128 0 64 128
  (interval_append test128 0 32 64
  (interval_append test128 0 16 32
  test128_block_0
  test128_block_1)
  (interval_append test128 32 48 64
  test128_block_2
  test128_block_3))
  (interval_append test128 64 96 128
  (interval_append test128 64 80 96
  test128_block_4
  test128_block_5)
  (interval_append test128 96 112 128
  test128_block_6
  test128_block_7)))
theorem routeInterval128 : Interval routeTest 128 256 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0722
