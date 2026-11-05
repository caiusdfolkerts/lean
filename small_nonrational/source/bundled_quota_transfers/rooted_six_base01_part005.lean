module
prelude
public import BundledQuotaTransfers.RootedSixBase01Part001
public import BundledQuotaTransfers.RootedSixBase01Part002
public import BundledQuotaTransfers.RootedSixBase01Part003
public import BundledQuotaTransfers.RootedSixBase01Part004
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0350Dispositions
public import RootedSubsumedForest0354Data
public import RootedSubsumedForest0353Dispositions
public import RootedSubsumedForest0355Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0348Proof026. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0348
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0348

/- Original module: RootedQuotaTransfer0348Proof027. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0348
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0348

/- Original module: RootedQuotaTransfer0348Proof028. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0348
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0348

/- Original module: RootedQuotaTransfer0348Proof029. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0348
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0348

/- Original module: RootedQuotaTransfer0348Proof030. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0348
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0348

/- Original module: RootedQuotaTransfer0348Proof031. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0348
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0348

/- Original module: RootedQuotaTransfer0348. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0348
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
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0348.quota
      ((RootedForests.RootedSubsumedForest0355.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0348.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0348.rawLeaves 89 RootedForests.RootedSubsumedForest0348.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0348.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0355.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0348

/- Original module: RootedQuotaTransfer0350Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0350
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 350: use the complete forest for case 354, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0350.quota k ≤ RootedForests.RootedSubsumedForest0354.quota k := by
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
(.branch 78
 (.branch 39
 (.branch 19
 (.leaf (.quota 1))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (.reuse 0))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 26
 (.leaf (.quota 1))
 (.branch 27
 (.leaf (.quota 1))
 (.branch 28
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.leaf (.quota 1))))
 (.branch 58
 (.leaf (.quota 1))
 (.branch 68
 (.branch 63
 (.branch 60
 (.leaf (.quota 1))
 (.branch 61
 (.leaf (.quota 1))
 (.branch 62
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 65
 (.leaf (.quota 1))
 (.branch 66
 (.leaf (.quota 1))
 (.branch 67
 (.leaf (.reuse 3))
 (.leaf (.quota 1))))))
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf (.quota 1))
 (.leaf (.reuse 4)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 117
 (.branch 97
 (.branch 87
 (.leaf (.quota 1))
 (.branch 92
 (.branch 89
 (.branch 88
 (.leaf (.quota 1))
 (.leaf (.reuse 5)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 107
 (.branch 102
 (.branch 99
 (.leaf (.quota 1))
 (.branch 100
 (.leaf (.reuse 6))
 (.leaf (.quota 1))))
 (.branch 104
 (.leaf (.quota 1))
 (.branch 105
 (.leaf (.reuse 7))
 (.branch 106
 (.leaf (.reuse 8))
 (.leaf (.quota 1))))))
 (.branch 112
 (.branch 109
 (.branch 108
 (.leaf (.quota 1))
 (.leaf (.reuse 9)))
 (.branch 110
 (.leaf (.reuse 10))
 (.leaf (.quota 1))))
 (.branch 114
 (.branch 113
 (.leaf (.reuse 11))
 (.leaf (.reuse 12)))
 (.leaf (.quota 1))))))
 (.branch 136
 (.branch 126
 (.branch 121
 (.branch 119
 (.leaf (.quota 1))
 (.branch 120
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 131
 (.leaf (.quota 1))
 (.branch 133
 (.leaf (.quota 1))
 (.branch 134
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 146
 (.leaf (.quota 1))
 (.branch 151
 (.branch 148
 (.leaf (.quota 1))
 (.branch 149
 (.leaf (.quota 1))
 (.branch 150
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1)))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0350.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0350.rawLeaves 17 (RootedForests.RootedSubsumedForest0354.rawLeaves i) (routes.get i)

def disposition (j : Fin 156) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0350.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0350

/- Original module: RootedQuotaTransfer0350Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0350
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0350

/- Original module: RootedQuotaTransfer0350Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0350
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 28 :=
  interval_of_check test128 16 12 (by decide +kernel)

theorem test128_complete : Interval test128 0 28 :=
  (interval_append test128 0 16 28
  test128_block_0
  test128_block_1)
theorem routeInterval128 : Interval routeTest 128 156 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0350

/- Original module: RootedQuotaTransfer0350. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0350
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 156 :=
  (interval_append routeTest 0 128 156
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 156) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0350.quota
      ((RootedForests.RootedSubsumedForest0354.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0350.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0350.rawLeaves 17 RootedForests.RootedSubsumedForest0350.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0350.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0354.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0350

/- Original module: RootedQuotaTransfer0353Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0353
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 353: use the complete forest for case 355, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0353.quota k ≤ RootedForests.RootedSubsumedForest0355.quota k := by
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
(.branch 2042
 (.branch 1021
 (.branch 510
 (.branch 255
 (.branch 127
 (.branch 63
 (.branch 31
 (.leaf (.quota 1))
 (.branch 47
 (.branch 39
 (.leaf (.quota 1))
 (.branch 43
 (.leaf (.quota 1))
 (.branch 45
 (.branch 44
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 55
 (.leaf (.quota 1))
 (.branch 59
 (.branch 57
 (.branch 56
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 95
 (.branch 79
 (.branch 71
 (.branch 67
 (.branch 65
 (.branch 64
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 66
 (.leaf (.quota 2))
 (.leaf (.reuse 4))))
 (.branch 69
 (.branch 68
 (.leaf (.reuse 5))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 87
 (.branch 83
 (.leaf (.quota 1))
 (.branch 85
 (.leaf (.quota 1))
 (.branch 86
 (.leaf (.reuse 6))
 (.leaf (.quota 1)))))
 (.branch 91
 (.branch 89
 (.leaf (.quota 1))
 (.branch 90
 (.leaf (.reuse 7))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 111
 (.branch 103
 (.leaf (.quota 1))
 (.branch 107
 (.leaf (.quota 1))
 (.branch 109
 (.branch 108
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 119
 (.leaf (.quota 1))
 (.branch 123
 (.branch 121
 (.leaf (.quota 1))
 (.branch 122
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))
 (.branch 191
 (.branch 159
 (.branch 143
 (.branch 135
 (.branch 131
 (.branch 129
 (.branch 128
 (.leaf (.quota 1))
 (.leaf (.reuse 10)))
 (.branch 130
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 151
 (.leaf (.quota 1))
 (.branch 155
 (.branch 153
 (.branch 152
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 157
 (.branch 156
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 175
 (.branch 167
 (.branch 163
 (.branch 161
 (.branch 160
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 223
 (.leaf (.quota 1))
 (.branch 239
 (.leaf (.quota 1))
 (.branch 247
 (.branch 243
 (.leaf (.quota 1))
 (.branch 245
 (.leaf (.quota 1))
 (.branch 246
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 251
 (.branch 249
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 253
 (.leaf (.quota 1))
 (.branch 254
 (.leaf (.quota 1))
 (.leaf (.quota 3))))))))))
 (.branch 382
 (.branch 318
 (.branch 286
 (.branch 270
 (.branch 262
 (.branch 258
 (.leaf (.quota 1))
 (.branch 260
 (.leaf (.quota 1))
 (.branch 261
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 266
 (.branch 264
 (.branch 263
 (.leaf (.reuse 23))
 (.leaf (.quota 1)))
 (.branch 265
 (.leaf (.quota 1))
 (.leaf (.reuse 24))))
 (.branch 268
 (.branch 267
 (.leaf (.quota 1))
 (.leaf (.reuse 25)))
 (.leaf (.quota 1)))))
 (.branch 278
 (.leaf (.quota 1))
 (.branch 282
 (.leaf (.quota 1))
 (.branch 284
 (.branch 283
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 302
 (.branch 294
 (.branch 290
 (.branch 288
 (.leaf (.quota 1))
 (.branch 289
 (.leaf (.quota 1))
 (.leaf (.reuse 28))))
 (.branch 292
 (.leaf (.quota 1))
 (.branch 293
 (.leaf (.quota 1))
 (.leaf (.reuse 29)))))
 (.branch 298
 (.branch 296
 (.branch 295
 (.leaf (.reuse 30))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 310
 (.branch 306
 (.branch 304
 (.leaf (.quota 1))
 (.branch 305
 (.leaf (.quota 1))
 (.leaf (.reuse 31))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 350
 (.branch 334
 (.branch 326
 (.branch 322
 (.leaf (.quota 1))
 (.branch 324
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 330
 (.branch 328
 (.branch 327
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 332
 (.leaf (.quota 1))
 (.branch 333
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 342
 (.leaf (.quota 1))
 (.branch 346
 (.branch 344
 (.leaf (.quota 1))
 (.branch 345
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))
 (.branch 366
 (.branch 358
 (.leaf (.quota 1))
 (.branch 362
 (.leaf (.quota 1))
 (.branch 364
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 374
 (.branch 370
 (.leaf (.quota 1))
 (.branch 372
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 446
 (.branch 414
 (.branch 398
 (.branch 390
 (.branch 386
 (.leaf (.quota 1))
 (.branch 388
 (.branch 387
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 406
 (.branch 402
 (.branch 400
 (.branch 399
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 430
 (.branch 422
 (.leaf (.quota 1))
 (.branch 426
 (.branch 424
 (.leaf (.quota 1))
 (.branch 425
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 478
 (.branch 462
 (.leaf (.quota 1))
 (.branch 470
 (.leaf (.quota 1))
 (.branch 474
 (.leaf (.quota 1))
 (.branch 476
 (.leaf (.quota 1))
 (.branch 477
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 494
 (.branch 486
 (.branch 482
 (.leaf (.quota 1))
 (.branch 484
 (.leaf (.quota 1))
 (.branch 485
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 502
 (.branch 498
 (.branch 496
 (.branch 495
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 500
 (.leaf (.quota 1))
 (.branch 501
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))))))
 (.branch 765
 (.branch 637
 (.branch 573
 (.branch 541
 (.branch 525
 (.branch 517
 (.leaf (.quota 1))
 (.branch 521
 (.leaf (.quota 1))
 (.branch 523
 (.branch 522
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 533
 (.branch 529
 (.branch 527
 (.leaf (.quota 1))
 (.branch 528
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 605
 (.branch 589
 (.branch 581
 (.leaf (.quota 1))
 (.branch 585
 (.leaf (.quota 1))
 (.branch 587
 (.branch 586
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 597
 (.branch 593
 (.branch 591
 (.leaf (.quota 1))
 (.branch 592
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 621
 (.branch 613
 (.branch 609
 (.leaf (.quota 1))
 (.branch 611
 (.leaf (.quota 1))
 (.branch 612
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 701
 (.branch 669
 (.branch 653
 (.leaf (.quota 1))
 (.branch 661
 (.leaf (.quota 1))
 (.branch 665
 (.leaf (.quota 1))
 (.branch 667
 (.branch 666
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 668
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 685
 (.branch 677
 (.leaf (.quota 1))
 (.branch 681
 (.branch 679
 (.branch 678
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 683
 (.branch 682
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 693
 (.leaf (.quota 1))
 (.branch 697
 (.leaf (.quota 1))
 (.branch 699
 (.branch 698
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 733
 (.leaf (.quota 1))
 (.branch 749
 (.branch 741
 (.branch 737
 (.branch 735
 (.leaf (.quota 1))
 (.branch 736
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 757
 (.branch 753
 (.leaf (.quota 1))
 (.branch 755
 (.branch 754
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 756
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 761
 (.branch 759
 (.leaf (.quota 1))
 (.branch 760
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 763
 (.branch 762
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))))
 (.branch 893
 (.branch 829
 (.branch 797
 (.branch 781
 (.branch 773
 (.leaf (.quota 1))
 (.branch 777
 (.leaf (.quota 1))
 (.branch 779
 (.leaf (.quota 1))
 (.branch 780
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 789
 (.branch 785
 (.leaf (.quota 1))
 (.branch 787
 (.branch 786
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 793
 (.branch 791
 (.branch 790
 (.leaf (.quota 1))
 (.leaf (.reuse 67)))
 (.branch 792
 (.leaf (.quota 1))
 (.leaf (.reuse 68))))
 (.leaf (.quota 1)))))
 (.branch 813
 (.branch 805
 (.leaf (.quota 1))
 (.branch 809
 (.leaf (.quota 1))
 (.branch 811
 (.leaf (.quota 1))
 (.branch 812
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.branch 821
 (.branch 817
 (.branch 815
 (.branch 814
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 819
 (.branch 818
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 825
 (.branch 823
 (.leaf (.quota 1))
 (.branch 824
 (.leaf (.quota 1))
 (.leaf (.reuse 73))))
 (.leaf (.quota 1))))))
 (.branch 861
 (.leaf (.quota 1))
 (.branch 877
 (.branch 869
 (.branch 865
 (.branch 863
 (.leaf (.quota 1))
 (.branch 864
 (.leaf (.reuse 74))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 873
 (.branch 871
 (.leaf (.quota 1))
 (.branch 872
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 885
 (.branch 881
 (.branch 879
 (.branch 878
 (.leaf (.reuse 76))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 883
 (.branch 882
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 889
 (.leaf (.quota 1))
 (.branch 891
 (.leaf (.quota 1))
 (.branch 892
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 957
 (.branch 925
 (.branch 909
 (.branch 901
 (.branch 897
 (.branch 895
 (.branch 894
 (.leaf (.reuse 79))
 (.leaf (.quota 1)))
 (.branch 896
 (.leaf (.quota 1))
 (.leaf (.reuse 80))))
 (.branch 899
 (.branch 898
 (.leaf (.reuse 81))
 (.leaf (.reuse 82)))
 (.branch 900
 (.leaf (.reuse 83))
 (.leaf (.reuse 84)))))
 (.branch 905
 (.branch 903
 (.branch 902
 (.leaf (.quota 1))
 (.leaf (.reuse 85)))
 (.branch 904
 (.leaf (.reuse 86))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 941
 (.branch 933
 (.branch 929
 (.leaf (.quota 1))
 (.branch 931
 (.leaf (.quota 1))
 (.branch 932
 (.leaf (.quota 1))
 (.leaf (.reuse 87)))))
 (.branch 937
 (.branch 935
 (.leaf (.quota 1))
 (.branch 936
 (.leaf (.reuse 88))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 989
 (.branch 973
 (.leaf (.quota 1))
 (.branch 981
 (.branch 977
 (.leaf (.quota 1))
 (.branch 979
 (.branch 978
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 985
 (.leaf (.quota 1))
 (.branch 987
 (.branch 986
 (.leaf (.quota 1))
 (.leaf (.reuse 90)))
 (.leaf (.quota 1))))))
 (.branch 1005
 (.branch 997
 (.branch 993
 (.branch 991
 (.leaf (.quota 1))
 (.branch 992
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 995
 (.branch 994
 (.leaf (.reuse 93))
 (.leaf (.reuse 94)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1013
 (.branch 1009
 (.branch 1007
 (.leaf (.quota 1))
 (.branch 1008
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1017
 (.branch 1015
 (.branch 1014
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))))
 (.branch 1531
 (.branch 1276
 (.branch 1148
 (.branch 1084
 (.branch 1052
 (.branch 1036
 (.branch 1028
 (.branch 1024
 (.leaf (.quota 1))
 (.branch 1026
 (.branch 1025
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1027
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1032
 (.leaf (.quota 1))
 (.branch 1034
 (.branch 1033
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 1068
 (.branch 1060
 (.leaf (.quota 1))
 (.branch 1064
 (.branch 1062
 (.branch 1061
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1066
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1076
 (.branch 1072
 (.branch 1070
 (.leaf (.quota 1))
 (.branch 1071
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 1080
 (.branch 1078
 (.leaf (.quota 1))
 (.branch 1079
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1082
 (.leaf (.quota 1))
 (.branch 1083
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 1116
 (.branch 1100
 (.branch 1092
 (.leaf (.quota 1))
 (.branch 1096
 (.branch 1094
 (.leaf (.quota 1))
 (.branch 1095
 (.leaf (.reuse 106))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 1108
 (.branch 1104
 (.branch 1102
 (.leaf (.quota 1))
 (.branch 1103
 (.leaf (.reuse 108))
 (.leaf (.reuse 109))))
 (.branch 1106
 (.branch 1105
 (.leaf (.reuse 110))
 (.leaf (.reuse 111)))
 (.leaf (.quota 1))))
 (.branch 1112
 (.branch 1110
 (.branch 1109
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1111
 (.leaf (.quota 1))
 (.leaf (.reuse 115))))
 (.branch 1114
 (.branch 1113
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1115
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1132
 (.branch 1124
 (.branch 1120
 (.branch 1118
 (.leaf (.quota 1))
 (.branch 1119
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 1128
 (.branch 1126
 (.leaf (.quota 1))
 (.branch 1127
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1130
 (.leaf (.quota 1))
 (.branch 1131
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1140
 (.branch 1136
 (.branch 1134
 (.leaf (.quota 1))
 (.branch 1135
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1138
 (.leaf (.quota 1))
 (.branch 1139
 (.leaf (.quota 1))
 (.leaf (.reuse 123)))))
 (.leaf (.quota 1))))))
 (.branch 1212
 (.branch 1180
 (.branch 1164
 (.branch 1156
 (.leaf (.quota 1))
 (.branch 1160
 (.leaf (.quota 1))
 (.branch 1162
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1172
 (.branch 1168
 (.leaf (.quota 1))
 (.branch 1170
 (.leaf (.quota 1))
 (.branch 1171
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1176
 (.branch 1174
 (.leaf (.quota 1))
 (.branch 1175
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))
 (.branch 1196
 (.branch 1188
 (.leaf (.quota 1))
 (.branch 1192
 (.leaf (.quota 1))
 (.branch 1194
 (.leaf (.quota 1))
 (.branch 1195
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1204
 (.branch 1200
 (.branch 1198
 (.leaf (.quota 1))
 (.branch 1199
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1244
 (.branch 1228
 (.branch 1220
 (.branch 1216
 (.branch 1214
 (.leaf (.quota 1))
 (.branch 1215
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1224
 (.branch 1222
 (.branch 1221
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1223
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1226
 (.leaf (.quota 1))
 (.branch 1227
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1236
 (.branch 1232
 (.branch 1230
 (.leaf (.quota 1))
 (.branch 1231
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 1240
 (.branch 1238
 (.branch 1237
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1260
 (.branch 1252
 (.branch 1248
 (.branch 1246
 (.leaf (.quota 1))
 (.branch 1247
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1250
 (.leaf (.quota 1))
 (.branch 1251
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1256
 (.branch 1254
 (.branch 1253
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 1403
 (.branch 1339
 (.branch 1307
 (.branch 1291
 (.branch 1283
 (.branch 1279
 (.leaf (.quota 1))
 (.branch 1281
 (.leaf (.quota 1))
 (.branch 1282
 (.leaf (.reuse 140))
 (.leaf (.quota 1)))))
 (.branch 1287
 (.branch 1285
 (.branch 1284
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1289
 (.leaf (.quota 1))
 (.branch 1290
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1299
 (.leaf (.quota 1))
 (.branch 1303
 (.branch 1301
 (.leaf (.quota 1))
 (.branch 1302
 (.leaf (.reuse 143))
 (.leaf (.reuse 144))))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 1371
 (.branch 1355
 (.branch 1347
 (.leaf (.quota 1))
 (.branch 1351
 (.leaf (.quota 1))
 (.branch 1353
 (.branch 1352
 (.leaf (.quota 1))
 (.leaf (.reuse 145)))
 (.leaf (.quota 1)))))
 (.branch 1363
 (.branch 1359
 (.branch 1357
 (.branch 1356
 (.leaf (.reuse 146))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1367
 (.leaf (.quota 1))
 (.branch 1369
 (.branch 1368
 (.leaf (.quota 1))
 (.leaf (.reuse 147)))
 (.leaf (.quota 1))))))
 (.branch 1387
 (.branch 1379
 (.branch 1375
 (.leaf (.quota 1))
 (.branch 1377
 (.branch 1376
 (.leaf (.quota 1))
 (.leaf (.reuse 148)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1395
 (.branch 1391
 (.leaf (.quota 1))
 (.branch 1393
 (.leaf (.quota 1))
 (.branch 1394
 (.leaf (.reuse 149))
 (.leaf (.quota 1)))))
 (.branch 1399
 (.branch 1397
 (.branch 1396
 (.leaf (.reuse 150))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 1467
 (.branch 1435
 (.branch 1419
 (.branch 1411
 (.branch 1407
 (.branch 1405
 (.leaf (.quota 1))
 (.branch 1406
 (.leaf (.reuse 151))
 (.leaf (.reuse 152))))
 (.branch 1409
 (.leaf (.quota 1))
 (.branch 1410
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1415
 (.branch 1413
 (.leaf (.quota 1))
 (.branch 1414
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1417
 (.leaf (.quota 1))
 (.branch 1418
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1427
 (.branch 1423
 (.leaf (.quota 1))
 (.branch 1425
 (.branch 1424
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 1451
 (.leaf (.quota 1))
 (.branch 1459
 (.branch 1455
 (.branch 1453
 (.leaf (.quota 1))
 (.branch 1454
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1457
 (.branch 1456
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1463
 (.branch 1461
 (.branch 1460
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1499
 (.branch 1483
 (.leaf (.quota 1))
 (.branch 1491
 (.branch 1487
 (.branch 1485
 (.leaf (.quota 1))
 (.branch 1486
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1489
 (.leaf (.quota 1))
 (.branch 1490
 (.leaf (.quota 1))
 (.leaf (.reuse 161)))))
 (.branch 1495
 (.leaf (.quota 1))
 (.branch 1497
 (.leaf (.quota 1))
 (.branch 1498
 (.leaf (.reuse 162))
 (.leaf (.reuse 163)))))))
 (.branch 1515
 (.branch 1507
 (.branch 1503
 (.branch 1501
 (.leaf (.quota 1))
 (.branch 1502
 (.leaf (.reuse 164))
 (.leaf (.quota 1))))
 (.branch 1505
 (.leaf (.quota 1))
 (.branch 1506
 (.leaf (.reuse 166))
 (.leaf (.reuse 167)))))
 (.branch 1511
 (.branch 1509
 (.leaf (.quota 1))
 (.branch 1510
 (.leaf (.quota 1))
 (.leaf (.reuse 168))))
 (.branch 1513
 (.branch 1512
 (.leaf (.reuse 169))
 (.leaf (.reuse 170)))
 (.branch 1514
 (.leaf (.quota 1))
 (.leaf (.reuse 171))))))
 (.branch 1523
 (.branch 1519
 (.branch 1517
 (.branch 1516
 (.leaf (.reuse 172))
 (.leaf (.quota 1)))
 (.branch 1518
 (.leaf (.reuse 174))
 (.leaf (.reuse 175))))
 (.leaf (.quota 1)))
 (.branch 1527
 (.branch 1525
 (.branch 1524
 (.leaf (.quota 1))
 (.leaf (.reuse 178)))
 (.branch 1526
 (.leaf (.reuse 179))
 (.leaf (.quota 1))))
 (.branch 1529
 (.branch 1528
 (.leaf (.quota 1))
 (.leaf (.reuse 180)))
 (.leaf (.quota 1))))))))))
 (.branch 1786
 (.branch 1658
 (.branch 1594
 (.branch 1562
 (.branch 1546
 (.branch 1538
 (.branch 1534
 (.leaf (.quota 1))
 (.branch 1536
 (.leaf (.quota 1))
 (.branch 1537
 (.leaf (.reuse 182))
 (.leaf (.quota 1)))))
 (.branch 1542
 (.branch 1540
 (.branch 1539
 (.leaf (.quota 1))
 (.leaf (.reuse 183)))
 (.branch 1541
 (.leaf (.quota 1))
 (.leaf (.reuse 184))))
 (.leaf (.quota 1))))
 (.branch 1554
 (.branch 1550
 (.branch 1548
 (.branch 1547
 (.leaf (.reuse 185))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1558
 (.leaf (.quota 1))
 (.branch 1560
 (.leaf (.quota 1))
 (.branch 1561
 (.leaf (.reuse 186))
 (.leaf (.reuse 187)))))))
 (.branch 1578
 (.branch 1570
 (.branch 1566
 (.leaf (.quota 1))
 (.branch 1568
 (.leaf (.quota 1))
 (.branch 1569
 (.leaf (.quota 1))
 (.leaf (.reuse 189)))))
 (.leaf (.quota 2)))
 (.branch 1586
 (.branch 1582
 (.branch 1580
 (.branch 1579
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1590
 (.leaf (.quota 1))
 (.branch 1592
 (.branch 1591
 (.leaf (.reuse 201))
 (.leaf (.reuse 202)))
 (.leaf (.quota 1)))))))
 (.branch 1626
 (.branch 1610
 (.branch 1602
 (.branch 1598
 (.branch 1596
 (.branch 1595
 (.leaf (.reuse 203))
 (.leaf (.quota 1)))
 (.branch 1597
 (.leaf (.quota 1))
 (.leaf (.reuse 204))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1618
 (.branch 1614
 (.branch 1612
 (.leaf (.quota 1))
 (.branch 1613
 (.leaf (.reuse 206))
 (.leaf (.reuse 207))))
 (.leaf (.quota 1)))
 (.branch 1622
 (.branch 1620
 (.branch 1619
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1642
 (.branch 1634
 (.branch 1630
 (.branch 1628
 (.leaf (.quota 1))
 (.branch 1629
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1650
 (.branch 1646
 (.leaf (.quota 1))
 (.branch 1648
 (.branch 1647
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1654
 (.branch 1652
 (.branch 1651
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1653
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1656
 (.branch 1655
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1657
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 1722
 (.branch 1690
 (.branch 1674
 (.branch 1666
 (.branch 1662
 (.branch 1660
 (.leaf (.quota 1))
 (.branch 1661
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 1670
 (.branch 1668
 (.leaf (.quota 1))
 (.branch 1669
 (.leaf (.reuse 216))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 1682
 (.leaf (.quota 1))
 (.branch 1686
 (.branch 1684
 (.leaf (.quota 2))
 (.branch 1685
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 1706
 (.leaf (.quota 1))
 (.branch 1714
 (.branch 1710
 (.leaf (.quota 1))
 (.branch 1712
 (.branch 1711
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 1718
 (.leaf (.quota 1))
 (.branch 1720
 (.leaf (.quota 1))
 (.branch 1721
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 1754
 (.leaf (.quota 1))
 (.branch 1770
 (.branch 1762
 (.branch 1758
 (.leaf (.quota 1))
 (.branch 1760
 (.branch 1759
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1761
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1766
 (.leaf (.quota 1))
 (.branch 1768
 (.leaf (.quota 1))
 (.branch 1769
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1778
 (.leaf (.quota 1))
 (.branch 1782
 (.leaf (.quota 1))
 (.branch 1784
 (.branch 1783
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))))))
 (.branch 1914
 (.branch 1850
 (.branch 1818
 (.branch 1802
 (.leaf (.quota 1))
 (.branch 1810
 (.branch 1806
 (.branch 1804
 (.leaf (.quota 1))
 (.branch 1805
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1834
 (.branch 1826
 (.branch 1822
 (.branch 1820
 (.branch 1819
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1830
 (.branch 1828
 (.leaf (.quota 1))
 (.branch 1829
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 1842
 (.leaf (.quota 1))
 (.branch 1846
 (.branch 1844
 (.leaf (.quota 1))
 (.branch 1845
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))))
 (.branch 1882
 (.branch 1866
 (.branch 1858
 (.branch 1854
 (.branch 1852
 (.leaf (.quota 1))
 (.branch 1853
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 1862
 (.branch 1860
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1874
 (.branch 1870
 (.leaf (.quota 1))
 (.branch 1872
 (.leaf (.quota 1))
 (.branch 1873
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 1898
 (.branch 1890
 (.branch 1886
 (.branch 1884
 (.leaf (.quota 1))
 (.branch 1885
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1894
 (.branch 1892
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1896
 (.branch 1895
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 1978
 (.branch 1946
 (.branch 1930
 (.branch 1922
 (.leaf (.quota 1))
 (.branch 1926
 (.leaf (.quota 1))
 (.branch 1928
 (.branch 1927
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 1938
 (.branch 1934
 (.branch 1932
 (.branch 1931
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1942
 (.branch 1940
 (.branch 1939
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1944
 (.leaf (.quota 2))
 (.branch 1945
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 1962
 (.branch 1954
 (.branch 1950
 (.branch 1948
 (.branch 1947
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1949
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1952
 (.leaf (.quota 1))
 (.branch 1953
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 1970
 (.branch 1966
 (.leaf (.quota 1))
 (.branch 1968
 (.leaf (.quota 1))
 (.branch 1969
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1974
 (.branch 1972
 (.branch 1971
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1976
 (.branch 1975
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))))
 (.branch 2010
 (.branch 1994
 (.branch 1986
 (.branch 1982
 (.branch 1980
 (.branch 1979
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 1984
 (.branch 1983
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1990
 (.branch 1988
 (.leaf (.quota 1))
 (.branch 1989
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 2002
 (.leaf (.quota 1))
 (.branch 2006
 (.branch 2004
 (.leaf (.quota 1))
 (.branch 2005
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2008
 (.branch 2007
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2009
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2026
 (.leaf (.quota 1))
 (.branch 2034
 (.branch 2030
 (.leaf (.quota 1))
 (.branch 2032
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2038
 (.branch 2036
 (.branch 2035
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2037
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2040
 (.branch 2039
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))))))
 (.branch 3063
 (.branch 2552
 (.branch 2297
 (.branch 2169
 (.branch 2105
 (.branch 2073
 (.branch 2057
 (.leaf (.quota 1))
 (.branch 2065
 (.leaf (.quota 1))
 (.branch 2069
 (.leaf (.quota 1))
 (.branch 2071
 (.branch 2070
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2072
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 2089
 (.branch 2081
 (.leaf (.quota 1))
 (.branch 2085
 (.branch 2083
 (.leaf (.quota 1))
 (.branch 2084
 (.leaf (.reuse 272))
 (.leaf (.quota 1))))
 (.branch 2087
 (.branch 2086
 (.leaf (.quota 1))
 (.leaf (.reuse 274)))
 (.leaf (.quota 2)))))
 (.branch 2097
 (.branch 2093
 (.leaf (.quota 1))
 (.branch 2095
 (.branch 2094
 (.leaf (.reuse 277))
 (.leaf (.quota 2)))
 (.branch 2096
 (.leaf (.reuse 279))
 (.leaf (.quota 1)))))
 (.branch 2101
 (.leaf (.quota 1))
 (.branch 2103
 (.branch 2102
 (.leaf (.quota 2))
 (.leaf (.reuse 281)))
 (.leaf (.quota 1)))))))
 (.branch 2137
 (.branch 2121
 (.branch 2113
 (.branch 2109
 (.branch 2107
 (.branch 2106
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2117
 (.leaf (.quota 1))
 (.branch 2119
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2129
 (.branch 2125
 (.branch 2123
 (.leaf (.quota 1))
 (.branch 2124
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2153
 (.branch 2145
 (.leaf (.quota 1))
 (.branch 2149
 (.leaf (.quota 1))
 (.branch 2151
 (.leaf (.quota 1))
 (.branch 2152
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2161
 (.branch 2157
 (.branch 2155
 (.leaf (.quota 1))
 (.branch 2156
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 2233
 (.branch 2201
 (.branch 2185
 (.branch 2177
 (.branch 2173
 (.branch 2171
 (.branch 2170
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2181
 (.leaf (.quota 1))
 (.branch 2183
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2193
 (.branch 2189
 (.branch 2187
 (.branch 2186
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2188
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2191
 (.branch 2190
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2265
 (.leaf (.quota 1))
 (.branch 2281
 (.branch 2273
 (.branch 2269
 (.leaf (.quota 1))
 (.branch 2271
 (.branch 2270
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2277
 (.branch 2275
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2289
 (.branch 2285
 (.branch 2283
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2287
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))
 (.branch 2424
 (.branch 2360
 (.branch 2328
 (.branch 2312
 (.branch 2304
 (.leaf (.quota 1))
 (.branch 2308
 (.branch 2306
 (.leaf (.quota 1))
 (.branch 2307
 (.leaf (.quota 1))
 (.leaf (.reuse 308))))
 (.branch 2310
 (.branch 2309
 (.leaf (.reuse 309))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2320
 (.branch 2316
 (.leaf (.quota 1))
 (.branch 2318
 (.branch 2317
 (.leaf (.quota 1))
 (.leaf (.reuse 310)))
 (.leaf (.quota 1))))
 (.branch 2324
 (.branch 2322
 (.leaf (.quota 1))
 (.branch 2323
 (.leaf (.quota 1))
 (.leaf (.reuse 312))))
 (.leaf (.quota 1)))))
 (.branch 2344
 (.branch 2336
 (.branch 2332
 (.branch 2330
 (.branch 2329
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2352
 (.branch 2348
 (.branch 2346
 (.branch 2345
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 2350
 (.leaf (.quota 1))
 (.branch 2351
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2356
 (.leaf (.quota 1))
 (.branch 2358
 (.branch 2357
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 2392
 (.branch 2376
 (.branch 2368
 (.leaf (.quota 1))
 (.branch 2372
 (.leaf (.quota 1))
 (.branch 2374
 (.branch 2373
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 2384
 (.leaf (.quota 1))
 (.branch 2388
 (.branch 2386
 (.branch 2385
 (.leaf (.quota 1))
 (.leaf (.reuse 322)))
 (.branch 2387
 (.leaf (.reuse 323))
 (.leaf (.quota 1))))
 (.branch 2390
 (.branch 2389
 (.leaf (.quota 1))
 (.leaf (.reuse 324)))
 (.leaf (.quota 1))))))
 (.branch 2408
 (.branch 2400
 (.branch 2396
 (.leaf (.quota 1))
 (.branch 2398
 (.branch 2397
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2399
 (.leaf (.reuse 326))
 (.leaf (.reuse 327)))))
 (.branch 2404
 (.leaf (.quota 1))
 (.branch 2406
 (.branch 2405
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 2416
 (.branch 2412
 (.leaf (.quota 1))
 (.branch 2414
 (.branch 2413
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 2420
 (.leaf (.quota 1))
 (.branch 2422
 (.branch 2421
 (.leaf (.reuse 330))
 (.leaf (.quota 1)))
 (.branch 2423
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 2488
 (.branch 2456
 (.branch 2440
 (.branch 2432
 (.branch 2428
 (.branch 2426
 (.leaf (.quota 1))
 (.branch 2427
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 2436
 (.branch 2434
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 2448
 (.branch 2444
 (.leaf (.quota 1))
 (.branch 2446
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2452
 (.branch 2450
 (.branch 2449
 (.leaf (.reuse 339))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 2454
 (.branch 2453
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2455
 (.leaf (.quota 1))
 (.leaf (.reuse 344)))))))
 (.branch 2472
 (.branch 2464
 (.branch 2460
 (.branch 2458
 (.branch 2457
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2462
 (.leaf (.quota 1))
 (.branch 2463
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2468
 (.leaf (.quota 1))
 (.branch 2470
 (.leaf (.quota 1))
 (.branch 2471
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2480
 (.leaf (.quota 1))
 (.branch 2484
 (.branch 2482
 (.leaf (.quota 1))
 (.branch 2483
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 2520
 (.branch 2504
 (.branch 2496
 (.branch 2492
 (.leaf (.quota 1))
 (.branch 2494
 (.leaf (.quota 1))
 (.branch 2495
 (.leaf (.reuse 350))
 (.leaf (.reuse 351)))))
 (.branch 2500
 (.branch 2498
 (.leaf (.quota 1))
 (.branch 2499
 (.leaf (.reuse 352))
 (.leaf (.quota 1))))
 (.branch 2502
 (.branch 2501
 (.leaf (.quota 1))
 (.leaf (.reuse 353)))
 (.branch 2503
 (.leaf (.reuse 354))
 (.leaf (.reuse 355))))))
 (.branch 2512
 (.branch 2508
 (.branch 2506
 (.branch 2505
 (.leaf (.reuse 356))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2516
 (.branch 2514
 (.leaf (.quota 1))
 (.branch 2515
 (.leaf (.reuse 360))
 (.leaf (.reuse 361))))
 (.branch 2518
 (.branch 2517
 (.leaf (.reuse 362))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 2536
 (.branch 2528
 (.branch 2524
 (.branch 2522
 (.branch 2521
 (.leaf (.reuse 364))
 (.leaf (.reuse 365)))
 (.branch 2523
 (.leaf (.reuse 366))
 (.leaf (.reuse 367))))
 (.branch 2526
 (.branch 2525
 (.leaf (.reuse 368))
 (.leaf (.quota 1)))
 (.branch 2527
 (.leaf (.reuse 369))
 (.leaf (.quota 1)))))
 (.branch 2532
 (.branch 2530
 (.branch 2529
 (.leaf (.reuse 370))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2534
 (.branch 2533
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2535
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))))))
 (.branch 2807
 (.branch 2679
 (.branch 2615
 (.branch 2583
 (.branch 2567
 (.branch 2559
 (.leaf (.quota 1))
 (.branch 2563
 (.branch 2561
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2565
 (.leaf (.quota 1))
 (.branch 2566
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2575
 (.branch 2571
 (.branch 2569
 (.leaf (.quota 1))
 (.branch 2570
 (.leaf (.quota 2))
 (.leaf (.reuse 379))))
 (.leaf (.quota 1)))
 (.branch 2579
 (.leaf (.quota 1))
 (.branch 2581
 (.branch 2580
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2582
 (.leaf (.reuse 382))
 (.leaf (.quota 1)))))))
 (.branch 2599
 (.branch 2591
 (.branch 2587
 (.leaf (.quota 1))
 (.branch 2589
 (.leaf (.quota 1))
 (.branch 2590
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1)))
 (.branch 2607
 (.branch 2603
 (.leaf (.quota 1))
 (.branch 2605
 (.leaf (.quota 1))
 (.branch 2606
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2611
 (.branch 2609
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 2647
 (.branch 2631
 (.branch 2623
 (.leaf (.quota 1))
 (.branch 2627
 (.leaf (.quota 1))
 (.branch 2629
 (.branch 2628
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 2639
 (.branch 2635
 (.branch 2633
 (.branch 2632
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2643
 (.branch 2641
 (.branch 2640
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2663
 (.branch 2655
 (.leaf (.quota 1))
 (.branch 2659
 (.leaf (.quota 1))
 (.branch 2661
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2671
 (.leaf (.quota 1))
 (.branch 2675
 (.branch 2673
 (.branch 2672
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 2743
 (.branch 2711
 (.branch 2695
 (.branch 2687
 (.branch 2683
 (.branch 2681
 (.branch 2680
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2682
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2703
 (.branch 2699
 (.branch 2697
 (.branch 2696
 (.leaf (.quota 1))
 (.leaf (.reuse 399)))
 (.branch 2698
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2701
 (.branch 2700
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2707
 (.branch 2705
 (.leaf (.quota 1))
 (.branch 2706
 (.leaf (.reuse 402))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 2727
 (.branch 2719
 (.leaf (.quota 1))
 (.branch 2723
 (.branch 2721
 (.branch 2720
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 2725
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2735
 (.branch 2731
 (.branch 2729
 (.leaf (.quota 1))
 (.branch 2730
 (.leaf (.reuse 408))
 (.leaf (.quota 1))))
 (.branch 2733
 (.leaf (.quota 1))
 (.branch 2734
 (.leaf (.quota 1))
 (.leaf (.reuse 411)))))
 (.branch 2739
 (.branch 2737
 (.branch 2736
 (.leaf (.reuse 412))
 (.leaf (.reuse 413)))
 (.branch 2738
 (.leaf (.reuse 414))
 (.leaf (.quota 1))))
 (.branch 2741
 (.branch 2740
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2742
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 2775
 (.branch 2759
 (.branch 2751
 (.leaf (.quota 1))
 (.branch 2755
 (.leaf (.quota 1))
 (.branch 2757
 (.branch 2756
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 2767
 (.branch 2763
 (.branch 2761
 (.branch 2760
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2791
 (.leaf (.quota 1))
 (.branch 2799
 (.branch 2795
 (.leaf (.quota 1))
 (.branch 2797
 (.leaf (.quota 1))
 (.branch 2798
 (.leaf (.quota 1))
 (.leaf (.reuse 423)))))
 (.branch 2803
 (.branch 2801
 (.leaf (.quota 1))
 (.branch 2802
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2805
 (.branch 2804
 (.leaf (.quota 2))
 (.leaf (.reuse 426)))
 (.branch 2806
 (.leaf (.reuse 427))
 (.leaf (.quota 1))))))))))
 (.branch 2935
 (.branch 2871
 (.branch 2839
 (.branch 2823
 (.branch 2815
 (.branch 2811
 (.leaf (.quota 1))
 (.branch 2813
 (.branch 2812
 (.leaf (.reuse 428))
 (.leaf (.quota 1)))
 (.branch 2814
 (.leaf (.reuse 429))
 (.leaf (.quota 1)))))
 (.branch 2819
 (.branch 2817
 (.leaf (.quota 1))
 (.branch 2818
 (.leaf (.quota 1))
 (.leaf (.reuse 430))))
 (.branch 2821
 (.branch 2820
 (.leaf (.reuse 431))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2831
 (.branch 2827
 (.leaf (.quota 1))
 (.branch 2829
 (.leaf (.quota 1))
 (.branch 2830
 (.leaf (.reuse 432))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 2855
 (.branch 2847
 (.leaf (.quota 1))
 (.branch 2851
 (.leaf (.quota 1))
 (.branch 2853
 (.leaf (.quota 1))
 (.branch 2854
 (.leaf (.quota 1))
 (.leaf (.reuse 433))))))
 (.branch 2863
 (.leaf (.quota 1))
 (.branch 2867
 (.leaf (.quota 1))
 (.branch 2869
 (.leaf (.quota 1))
 (.branch 2870
 (.leaf (.reuse 434))
 (.leaf (.reuse 435))))))))
 (.branch 2903
 (.branch 2887
 (.branch 2879
 (.branch 2875
 (.branch 2873
 (.leaf (.quota 1))
 (.branch 2874
 (.leaf (.quota 1))
 (.leaf (.reuse 436))))
 (.branch 2877
 (.branch 2876
 (.leaf (.reuse 437))
 (.leaf (.quota 1)))
 (.branch 2878
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2883
 (.branch 2881
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2885
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 2895
 (.branch 2891
 (.leaf (.quota 1))
 (.branch 2893
 (.branch 2892
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2894
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 2899
 (.leaf (.quota 1))
 (.branch 2901
 (.branch 2900
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 2902
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 2919
 (.branch 2911
 (.branch 2907
 (.branch 2905
 (.leaf (.quota 1))
 (.branch 2906
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2909
 (.leaf (.quota 1))
 (.branch 2910
 (.leaf (.quota 1))
 (.leaf (.reuse 448)))))
 (.branch 2915
 (.branch 2913
 (.branch 2912
 (.leaf (.reuse 449))
 (.leaf (.quota 1)))
 (.branch 2914
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 2917
 (.leaf (.quota 1))
 (.branch 2918
 (.leaf (.quota 1))
 (.leaf (.reuse 451))))))
 (.branch 2927
 (.branch 2923
 (.branch 2921
 (.branch 2920
 (.leaf (.reuse 452))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2931
 (.branch 2929
 (.branch 2928
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 2930
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 2933
 (.leaf (.quota 1))
 (.branch 2934
 (.leaf (.reuse 455))
 (.leaf (.quota 1)))))))))
 (.branch 2999
 (.branch 2967
 (.branch 2951
 (.leaf (.quota 1))
 (.branch 2959
 (.leaf (.quota 1))
 (.branch 2963
 (.leaf (.quota 1))
 (.branch 2965
 (.branch 2964
 (.leaf (.reuse 456))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 2983
 (.branch 2975
 (.branch 2971
 (.leaf (.quota 1))
 (.branch 2973
 (.branch 2972
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 2979
 (.branch 2977
 (.branch 2976
 (.leaf (.quota 1))
 (.leaf (.reuse 458)))
 (.branch 2978
 (.leaf (.quota 1))
 (.leaf (.reuse 459))))
 (.branch 2981
 (.branch 2980
 (.leaf (.reuse 460))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 2991
 (.branch 2987
 (.branch 2985
 (.branch 2984
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 2989
 (.leaf (.quota 1))
 (.branch 2990
 (.leaf (.quota 1))
 (.leaf (.reuse 463)))))
 (.leaf (.quota 1)))))
 (.branch 3031
 (.branch 3015
 (.branch 3007
 (.leaf (.quota 1))
 (.branch 3011
 (.branch 3009
 (.leaf (.quota 1))
 (.branch 3010
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3013
 (.leaf (.quota 1))
 (.branch 3014
 (.leaf (.quota 1))
 (.leaf (.reuse 465))))))
 (.branch 3023
 (.leaf (.quota 1))
 (.branch 3027
 (.branch 3025
 (.leaf (.quota 1))
 (.branch 3026
 (.leaf (.reuse 466))
 (.leaf (.quota 1))))
 (.branch 3029
 (.leaf (.quota 1))
 (.branch 3030
 (.leaf (.quota 1))
 (.leaf (.reuse 468)))))))
 (.branch 3047
 (.branch 3039
 (.branch 3035
 (.leaf (.quota 1))
 (.branch 3037
 (.branch 3036
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 3055
 (.branch 3051
 (.leaf (.quota 1))
 (.branch 3053
 (.leaf (.quota 1))
 (.branch 3054
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1)))))))))
 (.branch 3573
 (.branch 3318
 (.branch 3190
 (.branch 3126
 (.branch 3094
 (.branch 3078
 (.branch 3070
 (.leaf (.quota 1))
 (.branch 3074
 (.branch 3072
 (.branch 3071
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3086
 (.branch 3082
 (.branch 3080
 (.branch 3079
 (.leaf (.quota 1))
 (.leaf (.reuse 476)))
 (.branch 3081
 (.leaf (.reuse 477))
 (.leaf (.quota 1))))
 (.branch 3084
 (.leaf (.quota 1))
 (.branch 3085
 (.leaf (.reuse 478))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1))))
 (.branch 3110
 (.branch 3102
 (.branch 3098
 (.branch 3096
 (.branch 3095
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3097
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 3106
 (.leaf (.quota 1))
 (.branch 3108
 (.leaf (.quota 1))
 (.branch 3109
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3118
 (.branch 3114
 (.branch 3112
 (.leaf (.quota 1))
 (.branch 3113
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 3122
 (.branch 3120
 (.branch 3119
 (.leaf (.quota 1))
 (.leaf (.reuse 485)))
 (.branch 3121
 (.leaf (.reuse 486))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 3158
 (.branch 3142
 (.branch 3134
 (.branch 3130
 (.branch 3128
 (.branch 3127
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 3132
 (.branch 3131
 (.leaf (.quota 1))
 (.leaf (.reuse 488)))
 (.branch 3133
 (.leaf (.reuse 489))
 (.leaf (.reuse 490)))))
 (.branch 3138
 (.branch 3136
 (.branch 3135
 (.leaf (.reuse 491))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3150
 (.leaf (.quota 1))
 (.branch 3154
 (.leaf (.quota 1))
 (.branch 3156
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3174
 (.branch 3166
 (.branch 3162
 (.branch 3160
 (.branch 3159
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3161
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3164
 (.leaf (.quota 1))
 (.branch 3165
 (.leaf (.quota 2))
 (.leaf (.reuse 499)))))
 (.leaf (.quota 1)))
 (.branch 3182
 (.branch 3178
 (.branch 3176
 (.branch 3175
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3180
 (.branch 3179
 (.leaf (.quota 1))
 (.leaf (.reuse 501)))
 (.branch 3181
 (.leaf (.reuse 502))
 (.leaf (.quota 1)))))
 (.branch 3186
 (.branch 3184
 (.branch 3183
 (.leaf (.quota 1))
 (.leaf (.reuse 503)))
 (.branch 3185
 (.leaf (.reuse 504))
 (.leaf (.quota 1))))
 (.branch 3188
 (.leaf (.quota 1))
 (.branch 3189
 (.leaf (.quota 1))
 (.leaf (.reuse 505)))))))))
 (.branch 3254
 (.branch 3222
 (.branch 3206
 (.branch 3198
 (.branch 3194
 (.branch 3192
 (.branch 3191
 (.leaf (.reuse 506))
 (.leaf (.reuse 507)))
 (.branch 3193
 (.leaf (.reuse 508))
 (.leaf (.quota 1))))
 (.branch 3196
 (.leaf (.quota 1))
 (.branch 3197
 (.leaf (.quota 1))
 (.leaf (.reuse 509)))))
 (.branch 3202
 (.branch 3200
 (.branch 3199
 (.leaf (.quota 1))
 (.leaf (.reuse 510)))
 (.leaf (.quota 1)))
 (.branch 3204
 (.branch 3203
 (.leaf (.quota 1))
 (.leaf (.reuse 511)))
 (.leaf (.quota 1)))))
 (.branch 3214
 (.branch 3210
 (.branch 3208
 (.leaf (.quota 1))
 (.branch 3209
 (.leaf (.quota 2))
 (.leaf (.reuse 513))))
 (.branch 3212
 (.branch 3211
 (.leaf (.quota 1))
 (.leaf (.reuse 514)))
 (.leaf (.quota 1))))
 (.branch 3218
 (.branch 3216
 (.branch 3215
 (.leaf (.reuse 515))
 (.leaf (.reuse 516)))
 (.leaf (.quota 1)))
 (.branch 3220
 (.branch 3219
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 3238
 (.branch 3230
 (.branch 3226
 (.branch 3224
 (.leaf (.quota 1))
 (.branch 3225
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 3234
 (.branch 3232
 (.branch 3231
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3246
 (.branch 3242
 (.leaf (.quota 1))
 (.branch 3244
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3250
 (.branch 3248
 (.leaf (.quota 1))
 (.branch 3249
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3252
 (.branch 3251
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3253
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 3286
 (.branch 3270
 (.branch 3262
 (.leaf (.quota 1))
 (.branch 3266
 (.leaf (.quota 1))
 (.branch 3268
 (.branch 3267
 (.leaf (.quota 1))
 (.leaf (.reuse 526)))
 (.branch 3269
 (.leaf (.reuse 527))
 (.leaf (.quota 1))))))
 (.branch 3278
 (.branch 3274
 (.branch 3272
 (.branch 3271
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 3282
 (.branch 3280
 (.branch 3279
 (.leaf (.quota 1))
 (.leaf (.reuse 531)))
 (.branch 3281
 (.leaf (.reuse 532))
 (.leaf (.quota 2))))
 (.branch 3284
 (.branch 3283
 (.leaf (.reuse 534))
 (.leaf (.reuse 535)))
 (.branch 3285
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 3302
 (.branch 3294
 (.branch 3290
 (.branch 3288
 (.branch 3287
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3289
 (.leaf (.reuse 538))
 (.leaf (.quota 2))))
 (.branch 3292
 (.branch 3291
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3293
 (.leaf (.quota 1))
 (.leaf (.reuse 541)))))
 (.branch 3298
 (.branch 3296
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3310
 (.branch 3306
 (.branch 3304
 (.branch 3303
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3305
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3308
 (.leaf (.quota 1))
 (.branch 3309
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3314
 (.leaf (.quota 1))
 (.branch 3316
 (.branch 3315
 (.leaf (.reuse 547))
 (.leaf (.reuse 548)))
 (.leaf (.quota 1)))))))))
 (.branch 3445
 (.branch 3381
 (.branch 3349
 (.branch 3333
 (.branch 3325
 (.branch 3321
 (.leaf (.quota 1))
 (.branch 3323
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3329
 (.leaf (.quota 1))
 (.branch 3331
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3341
 (.branch 3337
 (.branch 3335
 (.branch 3334
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3336
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3339
 (.branch 3338
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 3345
 (.branch 3343
 (.leaf (.quota 1))
 (.branch 3344
 (.leaf (.quota 1))
 (.leaf (.reuse 556))))
 (.branch 3347
 (.branch 3346
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 3365
 (.branch 3357
 (.branch 3353
 (.branch 3351
 (.leaf (.quota 1))
 (.branch 3352
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 3361
 (.branch 3359
 (.leaf (.quota 1))
 (.branch 3360
 (.leaf (.reuse 561))
 (.leaf (.quota 1))))
 (.branch 3363
 (.branch 3362
 (.leaf (.reuse 562))
 (.leaf (.reuse 563)))
 (.branch 3364
 (.leaf (.reuse 564))
 (.leaf (.reuse 565))))))
 (.branch 3373
 (.branch 3369
 (.branch 3367
 (.branch 3366
 (.leaf (.reuse 566))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3371
 (.branch 3370
 (.leaf (.reuse 567))
 (.leaf (.quota 1)))
 (.branch 3372
 (.leaf (.reuse 568))
 (.leaf (.quota 1)))))
 (.branch 3377
 (.branch 3375
 (.branch 3374
 (.leaf (.reuse 569))
 (.leaf (.reuse 570)))
 (.branch 3376
 (.leaf (.reuse 571))
 (.leaf (.quota 1))))
 (.branch 3379
 (.branch 3378
 (.leaf (.reuse 572))
 (.leaf (.reuse 573)))
 (.branch 3380
 (.leaf (.quota 1))
 (.leaf (.reuse 574))))))))
 (.branch 3413
 (.branch 3397
 (.branch 3389
 (.branch 3385
 (.branch 3383
 (.branch 3382
 (.leaf (.reuse 575))
 (.leaf (.reuse 576)))
 (.branch 3384
 (.leaf (.reuse 577))
 (.leaf (.reuse 578))))
 (.leaf (.quota 1)))
 (.branch 3393
 (.branch 3391
 (.branch 3390
 (.leaf (.reuse 579))
 (.leaf (.reuse 580)))
 (.branch 3392
 (.leaf (.reuse 581))
 (.leaf (.reuse 582))))
 (.leaf (.quota 1))))
 (.branch 3405
 (.branch 3401
 (.branch 3399
 (.branch 3398
 (.leaf (.reuse 583))
 (.leaf (.reuse 584)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3409
 (.branch 3407
 (.leaf (.quota 1))
 (.branch 3408
 (.leaf (.reuse 585))
 (.leaf (.reuse 586))))
 (.branch 3411
 (.branch 3410
 (.leaf (.quota 1))
 (.leaf (.reuse 587)))
 (.branch 3412
 (.leaf (.reuse 588))
 (.leaf (.reuse 589)))))))
 (.branch 3429
 (.branch 3421
 (.branch 3417
 (.branch 3415
 (.branch 3414
 (.leaf (.reuse 590))
 (.leaf (.reuse 591)))
 (.branch 3416
 (.leaf (.reuse 592))
 (.leaf (.reuse 593))))
 (.branch 3419
 (.branch 3418
 (.leaf (.reuse 594))
 (.leaf (.quota 1)))
 (.branch 3420
 (.leaf (.reuse 595))
 (.leaf (.quota 1)))))
 (.branch 3425
 (.branch 3423
 (.leaf (.quota 1))
 (.branch 3424
 (.leaf (.reuse 596))
 (.leaf (.quota 1))))
 (.branch 3427
 (.branch 3426
 (.leaf (.reuse 597))
 (.leaf (.reuse 598)))
 (.leaf (.quota 1)))))
 (.branch 3437
 (.branch 3433
 (.branch 3431
 (.branch 3430
 (.leaf (.reuse 599))
 (.leaf (.reuse 600)))
 (.leaf (.quota 1)))
 (.branch 3435
 (.branch 3434
 (.leaf (.quota 1))
 (.leaf (.reuse 601)))
 (.leaf (.quota 1))))
 (.branch 3441
 (.leaf (.quota 1))
 (.branch 3443
 (.leaf (.quota 1))
 (.branch 3444
 (.leaf (.reuse 602))
 (.leaf (.reuse 603)))))))))
 (.branch 3509
 (.branch 3477
 (.branch 3461
 (.branch 3453
 (.branch 3449
 (.branch 3447
 (.leaf (.quota 1))
 (.branch 3448
 (.leaf (.reuse 604))
 (.leaf (.quota 1))))
 (.branch 3451
 (.branch 3450
 (.leaf (.reuse 605))
 (.leaf (.reuse 606)))
 (.leaf (.quota 1))))
 (.branch 3457
 (.branch 3455
 (.leaf (.quota 1))
 (.branch 3456
 (.leaf (.reuse 607))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 3469
 (.leaf (.quota 1))
 (.branch 3473
 (.leaf (.quota 1))
 (.branch 3475
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3493
 (.leaf (.quota 1))
 (.branch 3501
 (.branch 3497
 (.branch 3495
 (.branch 3494
 (.leaf (.reuse 610))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3499
 (.leaf (.quota 1))
 (.branch 3500
 (.leaf (.quota 1))
 (.leaf (.reuse 612)))))
 (.branch 3505
 (.branch 3503
 (.branch 3502
 (.leaf (.reuse 613))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3507
 (.branch 3506
 (.leaf (.quota 1))
 (.leaf (.reuse 614)))
 (.branch 3508
 (.leaf (.reuse 615))
 (.leaf (.quota 1))))))))
 (.branch 3541
 (.branch 3525
 (.branch 3517
 (.branch 3513
 (.branch 3511
 (.branch 3510
 (.leaf (.quota 1))
 (.leaf (.reuse 616)))
 (.branch 3512
 (.leaf (.reuse 617))
 (.leaf (.reuse 618))))
 (.branch 3515
 (.branch 3514
 (.leaf (.reuse 619))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3521
 (.branch 3519
 (.branch 3518
 (.leaf (.reuse 622))
 (.leaf (.reuse 623)))
 (.branch 3520
 (.leaf (.reuse 624))
 (.leaf (.quota 1))))
 (.branch 3523
 (.branch 3522
 (.leaf (.quota 1))
 (.leaf (.reuse 625)))
 (.leaf (.quota 1)))))
 (.branch 3533
 (.branch 3529
 (.leaf (.quota 1))
 (.branch 3531
 (.branch 3530
 (.leaf (.reuse 626))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 3557
 (.leaf (.quota 1))
 (.branch 3565
 (.branch 3561
 (.branch 3559
 (.branch 3558
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3569
 (.branch 3567
 (.leaf (.quota 1))
 (.branch 3568
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))))))
 (.branch 3828
 (.branch 3700
 (.branch 3636
 (.branch 3604
 (.branch 3588
 (.branch 3580
 (.leaf (.quota 1))
 (.branch 3584
 (.branch 3582
 (.leaf (.quota 2))
 (.branch 3583
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3586
 (.leaf (.quota 1))
 (.branch 3587
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 3596
 (.branch 3592
 (.branch 3590
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3594
 (.branch 3593
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 3600
 (.branch 3598
 (.branch 3597
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 3620
 (.branch 3612
 (.leaf (.quota 1))
 (.branch 3616
 (.leaf (.quota 1))
 (.branch 3618
 (.branch 3617
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3619
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3628
 (.branch 3624
 (.leaf (.quota 1))
 (.branch 3626
 (.leaf (.quota 1))
 (.branch 3627
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3632
 (.branch 3630
 (.leaf (.quota 1))
 (.branch 3631
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))))
 (.branch 3668
 (.branch 3652
 (.branch 3644
 (.branch 3640
 (.leaf (.quota 1))
 (.branch 3642
 (.branch 3641
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 3648
 (.branch 3646
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3650
 (.leaf (.quota 1))
 (.branch 3651
 (.leaf (.quota 1))
 (.leaf (.reuse 648))))))
 (.branch 3660
 (.branch 3656
 (.branch 3654
 (.branch 3653
 (.leaf (.reuse 649))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3658
 (.branch 3657
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3659
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3664
 (.branch 3662
 (.branch 3661
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 3666
 (.branch 3665
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3667
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 3684
 (.branch 3676
 (.branch 3672
 (.branch 3670
 (.branch 3669
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3680
 (.leaf (.quota 1))
 (.branch 3682
 (.branch 3681
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 3692
 (.branch 3688
 (.leaf (.quota 1))
 (.branch 3690
 (.branch 3689
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 3696
 (.leaf (.quota 1))
 (.branch 3698
 (.branch 3697
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))))
 (.branch 3764
 (.branch 3732
 (.branch 3716
 (.branch 3708
 (.branch 3704
 (.leaf (.quota 1))
 (.branch 3706
 (.branch 3705
 (.leaf (.reuse 662))
 (.leaf (.reuse 663)))
 (.branch 3707
 (.leaf (.quota 1))
 (.leaf (.reuse 664)))))
 (.branch 3712
 (.branch 3710
 (.branch 3709
 (.leaf (.reuse 665))
 (.leaf (.quota 1)))
 (.branch 3711
 (.leaf (.reuse 666))
 (.leaf (.reuse 667))))
 (.leaf (.quota 1))))
 (.branch 3724
 (.leaf (.quota 1))
 (.branch 3728
 (.leaf (.quota 1))
 (.branch 3730
 (.branch 3729
 (.leaf (.quota 1))
 (.leaf (.reuse 668)))
 (.leaf (.quota 1))))))
 (.branch 3748
 (.leaf (.quota 1))
 (.branch 3756
 (.leaf (.quota 1))
 (.branch 3760
 (.leaf (.quota 1))
 (.branch 3762
 (.branch 3761
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 3796
 (.branch 3780
 (.branch 3772
 (.branch 3768
 (.leaf (.quota 1))
 (.branch 3770
 (.branch 3769
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3776
 (.branch 3774
 (.branch 3773
 (.leaf (.quota 1))
 (.leaf (.reuse 672)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3788
 (.branch 3784
 (.branch 3782
 (.leaf (.quota 1))
 (.branch 3783
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3786
 (.branch 3785
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3792
 (.branch 3790
 (.branch 3789
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3791
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 3794
 (.leaf (.quota 1))
 (.branch 3795
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 3812
 (.branch 3804
 (.branch 3800
 (.leaf (.quota 1))
 (.branch 3802
 (.leaf (.quota 2))
 (.branch 3803
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3808
 (.leaf (.quota 1))
 (.branch 3810
 (.branch 3809
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 3820
 (.branch 3816
 (.branch 3814
 (.branch 3813
 (.leaf (.reuse 682))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3818
 (.leaf (.quota 1))
 (.branch 3819
 (.leaf (.reuse 683))
 (.leaf (.quota 1)))))
 (.branch 3824
 (.branch 3822
 (.branch 3821
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 3826
 (.branch 3825
 (.leaf (.reuse 685))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))))
 (.branch 3956
 (.branch 3892
 (.branch 3860
 (.branch 3844
 (.branch 3836
 (.branch 3832
 (.branch 3830
 (.leaf (.quota 1))
 (.branch 3831
 (.leaf (.reuse 686))
 (.leaf (.quota 1))))
 (.branch 3834
 (.leaf (.quota 1))
 (.branch 3835
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 3852
 (.branch 3848
 (.leaf (.quota 1))
 (.branch 3850
 (.leaf (.quota 1))
 (.branch 3851
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3856
 (.branch 3854
 (.leaf (.quota 1))
 (.branch 3855
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3858
 (.leaf (.quota 1))
 (.branch 3859
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 3876
 (.branch 3868
 (.branch 3864
 (.branch 3862
 (.branch 3861
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3863
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 3872
 (.leaf (.quota 1))
 (.branch 3874
 (.branch 3873
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 3924
 (.branch 3908
 (.branch 3900
 (.branch 3896
 (.branch 3894
 (.branch 3893
 (.leaf (.quota 1))
 (.leaf (.reuse 694)))
 (.leaf (.quota 1)))
 (.branch 3898
 (.branch 3897
 (.leaf (.quota 1))
 (.leaf (.reuse 697)))
 (.leaf (.quota 1))))
 (.branch 3904
 (.branch 3902
 (.leaf (.quota 2))
 (.branch 3903
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3906
 (.branch 3905
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3907
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3916
 (.leaf (.quota 1))
 (.branch 3920
 (.leaf (.quota 1))
 (.branch 3922
 (.leaf (.quota 1))
 (.branch 3923
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 3940
 (.branch 3932
 (.branch 3928
 (.branch 3926
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 3930
 (.leaf (.quota 1))
 (.branch 3931
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 3936
 (.branch 3934
 (.leaf (.quota 1))
 (.branch 3935
 (.leaf (.quota 1))
 (.leaf (.reuse 708))))
 (.branch 3938
 (.branch 3937
 (.leaf (.reuse 709))
 (.leaf (.quota 2)))
 (.branch 3939
 (.leaf (.quota 1))
 (.leaf (.reuse 711))))))
 (.branch 3948
 (.branch 3944
 (.branch 3942
 (.branch 3941
 (.leaf (.reuse 712))
 (.leaf (.quota 1)))
 (.branch 3943
 (.leaf (.reuse 713))
 (.leaf (.reuse 714))))
 (.branch 3946
 (.leaf (.quota 1))
 (.branch 3947
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3952
 (.branch 3950
 (.branch 3949
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 4020
 (.branch 3988
 (.branch 3972
 (.branch 3964
 (.branch 3960
 (.leaf (.quota 1))
 (.branch 3962
 (.branch 3961
 (.leaf (.quota 1))
 (.leaf (.reuse 718)))
 (.leaf (.quota 1))))
 (.branch 3968
 (.branch 3966
 (.leaf (.quota 1))
 (.branch 3967
 (.leaf (.reuse 721))
 (.leaf (.quota 2))))
 (.branch 3970
 (.leaf (.quota 1))
 (.branch 3971
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 3980
 (.branch 3976
 (.branch 3974
 (.leaf (.quota 1))
 (.branch 3975
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 3978
 (.leaf (.quota 1))
 (.branch 3979
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 3984
 (.branch 3982
 (.branch 3981
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 3983
 (.leaf (.reuse 728))
 (.leaf (.quota 1))))
 (.branch 3986
 (.leaf (.quota 1))
 (.branch 3987
 (.leaf (.quota 1))
 (.leaf (.reuse 729)))))))
 (.branch 4004
 (.branch 3996
 (.branch 3992
 (.branch 3990
 (.branch 3989
 (.leaf (.reuse 730))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3994
 (.branch 3993
 (.leaf (.quota 1))
 (.leaf (.reuse 731)))
 (.branch 3995
 (.leaf (.reuse 732))
 (.leaf (.reuse 733)))))
 (.branch 4000
 (.leaf (.quota 1))
 (.branch 4002
 (.branch 4001
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 4012
 (.branch 4008
 (.leaf (.quota 1))
 (.branch 4010
 (.branch 4009
 (.leaf (.reuse 736))
 (.leaf (.quota 1)))
 (.branch 4011
 (.leaf (.reuse 737))
 (.leaf (.quota 1)))))
 (.branch 4016
 (.branch 4014
 (.leaf (.quota 1))
 (.branch 4015
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 4018
 (.branch 4017
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 4052
 (.branch 4036
 (.branch 4028
 (.branch 4024
 (.branch 4022
 (.branch 4021
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 4032
 (.leaf (.quota 1))
 (.branch 4034
 (.branch 4033
 (.leaf (.reuse 742))
 (.leaf (.reuse 743)))
 (.branch 4035
 (.leaf (.reuse 744))
 (.leaf (.quota 1))))))
 (.branch 4044
 (.branch 4040
 (.branch 4038
 (.branch 4037
 (.leaf (.reuse 745))
 (.leaf (.reuse 746)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 4048
 (.branch 4046
 (.branch 4045
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 4047
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 4068
 (.branch 4060
 (.branch 4056
 (.branch 4054
 (.branch 4053
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 4064
 (.leaf (.quota 1))
 (.branch 4066
 (.branch 4065
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 4076
 (.branch 4072
 (.branch 4070
 (.leaf (.quota 1))
 (.branch 4071
 (.leaf (.reuse 752))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 4080
 (.branch 4078
 (.leaf (.quota 1))
 (.branch 4079
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 4082
 (.branch 4081
 (.leaf (.reuse 754))
 (.leaf (.reuse 755)))
 (.leaf (.quota 1)))))))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0353.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0353.rawLeaves 756 (RootedForests.RootedSubsumedForest0355.rawLeaves i) (routes.get i)

def disposition (j : Fin 4084) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0353.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0353
