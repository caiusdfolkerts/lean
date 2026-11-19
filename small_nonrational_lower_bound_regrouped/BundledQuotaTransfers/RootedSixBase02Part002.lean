module
prelude
public import BundledQuotaTransfers.RootedSixBase02Part001
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0362Dispositions
public import RootedSubsumedForest0365Data
public import RootedSubsumedForest0364Dispositions
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0360Proof007. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test896 (i : Nat) := routeTest (i + 896)
theorem test896_block_0 : Interval test896 0 16 :=
  interval_of_check test896 0 16 (by decide +kernel)

theorem test896_block_1 : Interval test896 16 32 :=
  interval_of_check test896 16 16 (by decide +kernel)

theorem test896_block_2 : Interval test896 32 48 :=
  interval_of_check test896 32 16 (by decide +kernel)

theorem test896_block_3 : Interval test896 48 64 :=
  interval_of_check test896 48 16 (by decide +kernel)

theorem test896_block_4 : Interval test896 64 80 :=
  interval_of_check test896 64 16 (by decide +kernel)

theorem test896_block_5 : Interval test896 80 96 :=
  interval_of_check test896 80 16 (by decide +kernel)

theorem test896_block_6 : Interval test896 96 112 :=
  interval_of_check test896 96 16 (by decide +kernel)

theorem test896_block_7 : Interval test896 112 128 :=
  interval_of_check test896 112 16 (by decide +kernel)

theorem test896_complete : Interval test896 0 128 :=
  (interval_append test896 0 64 128
  (interval_append test896 0 32 64
  (interval_append test896 0 16 32
  test896_block_0
  test896_block_1)
  (interval_append test896 32 48 64
  test896_block_2
  test896_block_3))
  (interval_append test896 64 96 128
  (interval_append test896 64 80 96
  test896_block_4
  test896_block_5)
  (interval_append test896 96 112 128
  test896_block_6
  test896_block_7)))
theorem routeInterval896 : Interval routeTest 896 1024 := by
  intro i hlo hhi
  have h := test896_complete (i - 896) (Nat.zero_le _) (by omega)
  simpa only [test896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof008. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof009. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof010. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof011. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof012. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0360.quota
      ((RootedForests.RootedSubsumedForest0708.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0360.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0360.rawLeaves 55 RootedForests.RootedSubsumedForest0360.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0360.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0708.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0362Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0362
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 362: use the complete forest for case 365, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0362.quota k ≤ RootedForests.RootedSubsumedForest0365.quota k := by
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
(.branch 96
 (.branch 48
 (.branch 24
 (.branch 12
 (.branch 6
 (.leaf (.quota 1))
 (.branch 9
 (.leaf (.quota 1))
 (.branch 10
 (.leaf (.quota 1))
 (.branch 11
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))
 (.branch 36
 (.leaf (.quota 1))
 (.branch 42
 (.leaf (.quota 1))
 (.branch 45
 (.branch 43
 (.leaf (.quota 1))
 (.branch 44
 (.leaf (.reuse 1))
 (.leaf (.quota 1))))
 (.branch 46
 (.leaf (.reuse 2))
 (.leaf (.quota 1)))))))
 (.branch 72
 (.branch 60
 (.branch 54
 (.branch 51
 (.leaf (.quota 1))
 (.branch 52
 (.leaf (.quota 1))
 (.branch 53
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 57
 (.leaf (.quota 1))
 (.branch 58
 (.leaf (.quota 1))
 (.branch 59
 (.leaf (.reuse 4))
 (.leaf (.quota 1))))))
 (.branch 66
 (.branch 63
 (.branch 61
 (.leaf (.quota 1))
 (.branch 62
 (.leaf (.reuse 5))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 84
 (.leaf (.quota 1))
 (.branch 90
 (.branch 87
 (.leaf (.quota 1))
 (.branch 88
 (.leaf (.quota 1))
 (.branch 89
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1))))))
 (.branch 144
 (.branch 120
 (.branch 108
 (.branch 102
 (.branch 99
 (.branch 97
 (.leaf (.quota 1))
 (.branch 98
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 100
 (.leaf (.quota 1))
 (.branch 101
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 105
 (.branch 103
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 132
 (.branch 126
 (.leaf (.quota 1))
 (.branch 129
 (.branch 127
 (.leaf (.quota 1))
 (.branch 128
 (.leaf (.quota 1))
 (.leaf (.reuse 12))))
 (.leaf (.quota 1))))
 (.branch 138
 (.branch 135
 (.leaf (.quota 1))
 (.branch 136
 (.leaf (.quota 1))
 (.branch 137
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 141
 (.branch 139
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 168
 (.branch 156
 (.leaf (.quota 1))
 (.branch 162
 (.branch 159
 (.branch 157
 (.leaf (.quota 1))
 (.branch 158
 (.leaf (.reuse 15))
 (.leaf (.quota 1))))
 (.branch 160
 (.leaf (.reuse 16))
 (.branch 161
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 165
 (.branch 163
 (.leaf (.quota 1))
 (.branch 164
 (.leaf (.reuse 18))
 (.leaf (.reuse 19))))
 (.leaf (.quota 1)))))
 (.branch 180
 (.branch 174
 (.leaf (.quota 1))
 (.branch 177
 (.branch 175
 (.leaf (.quota 1))
 (.branch 176
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 178
 (.leaf (.quota 2))
 (.branch 179
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 186
 (.branch 183
 (.branch 181
 (.leaf (.quota 1))
 (.branch 182
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 189
 (.branch 187
 (.leaf (.quota 1))
 (.branch 188
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0362.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0362.rawLeaves 25 (RootedForests.RootedSubsumedForest0365.rawLeaves i) (routes.get i)

def disposition (j : Fin 192) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0362.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0362

/- Original module: RootedQuotaTransfer0362Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0362
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0362

/- Original module: RootedQuotaTransfer0362Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0362
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

theorem test128_complete : Interval test128 0 64 :=
  (interval_append test128 0 32 64
  (interval_append test128 0 16 32
  test128_block_0
  test128_block_1)
  (interval_append test128 32 48 64
  test128_block_2
  test128_block_3))
theorem routeInterval128 : Interval routeTest 128 192 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0362

/- Original module: RootedQuotaTransfer0362. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0362
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 192 :=
  (interval_append routeTest 0 128 192
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 192) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0362.quota
      ((RootedForests.RootedSubsumedForest0365.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0362.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0362.rawLeaves 25 RootedForests.RootedSubsumedForest0362.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0362.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0365.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0362

/- Original module: RootedQuotaTransfer0364Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 364: use the complete forest for case 708, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0364.quota k ≤ RootedForests.RootedSubsumedForest0708.quota k := by
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
(.branch 815
 (.branch 407
 (.branch 203
 (.branch 101
 (.branch 50
 (.leaf (.quota 1))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf (.quota 1))
 (.branch 52
 (.leaf (.reuse 0))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 68
 (.branch 65
 (.leaf (.quota 1))
 (.branch 66
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 71
 (.leaf (.quota 1))
 (.branch 73
 (.branch 72
 (.leaf (.reuse 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 88
 (.leaf (.quota 1))
 (.branch 94
 (.branch 91
 (.branch 89
 (.leaf (.quota 1))
 (.branch 90
 (.leaf (.quota 1))
 (.leaf (.reuse 4))))
 (.leaf (.quota 1)))
 (.branch 97
 (.branch 95
 (.leaf (.quota 1))
 (.branch 96
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 99
 (.branch 98
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))
 (.branch 152
 (.branch 126
 (.branch 113
 (.branch 107
 (.leaf (.quota 1))
 (.branch 110
 (.branch 108
 (.leaf (.reuse 7))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 119
 (.leaf (.quota 1))
 (.branch 122
 (.leaf (.quota 1))
 (.branch 124
 (.leaf (.quota 1))
 (.branch 125
 (.leaf (.reuse 9))
 (.leaf (.reuse 10)))))))
 (.branch 139
 (.branch 132
 (.branch 129
 (.leaf (.quota 1))
 (.branch 130
 (.leaf (.quota 1))
 (.branch 131
 (.leaf (.reuse 11))
 (.leaf (.reuse 12)))))
 (.branch 135
 (.branch 133
 (.leaf (.reuse 13))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 177
 (.branch 164
 (.branch 158
 (.leaf (.quota 1))
 (.branch 161
 (.branch 159
 (.leaf (.quota 1))
 (.branch 160
 (.leaf (.reuse 15))
 (.leaf (.reuse 16))))
 (.branch 162
 (.leaf (.reuse 17))
 (.branch 163
 (.leaf (.reuse 18))
 (.leaf (.quota 1))))))
 (.branch 170
 (.leaf (.quota 1))
 (.branch 173
 (.branch 171
 (.leaf (.quota 1))
 (.branch 172
 (.leaf (.quota 1))
 (.leaf (.reuse 19))))
 (.branch 175
 (.branch 174
 (.leaf (.reuse 20))
 (.leaf (.reuse 21)))
 (.branch 176
 (.leaf (.reuse 22))
 (.leaf (.quota 1)))))))
 (.branch 190
 (.branch 183
 (.leaf (.quota 1))
 (.branch 186
 (.branch 184
 (.leaf (.quota 1))
 (.branch 185
 (.leaf (.quota 1))
 (.leaf (.reuse 24))))
 (.branch 188
 (.leaf (.quota 1))
 (.branch 189
 (.leaf (.reuse 25))
 (.leaf (.quota 1))))))
 (.branch 196
 (.branch 193
 (.leaf (.quota 1))
 (.branch 194
 (.leaf (.reuse 26))
 (.branch 195
 (.leaf (.reuse 27))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))))
 (.branch 305
 (.branch 254
 (.branch 228
 (.branch 215
 (.branch 209
 (.leaf (.quota 1))
 (.branch 212
 (.leaf (.quota 1))
 (.branch 213
 (.leaf (.quota 1))
 (.branch 214
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 221
 (.branch 218
 (.branch 216
 (.leaf (.quota 2))
 (.branch 217
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 219
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 224
 (.branch 222
 (.leaf (.quota 2))
 (.branch 223
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 226
 (.leaf (.quota 1))
 (.branch 227
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 241
 (.branch 234
 (.leaf (.quota 1))
 (.branch 237
 (.branch 235
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 239
 (.leaf (.quota 1))
 (.branch 240
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 247
 (.branch 244
 (.leaf (.quota 1))
 (.branch 245
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))
 (.branch 279
 (.branch 266
 (.branch 260
 (.branch 257
 (.leaf (.quota 1))
 (.branch 258
 (.leaf (.quota 1))
 (.branch 259
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 263
 (.branch 261
 (.leaf (.quota 1))
 (.branch 262
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 272
 (.branch 269
 (.branch 267
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 292
 (.branch 285
 (.branch 282
 (.branch 280
 (.leaf (.quota 1))
 (.branch 281
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 283
 (.leaf (.quota 1))
 (.branch 284
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 298
 (.leaf (.quota 1))
 (.branch 301
 (.leaf (.quota 1))
 (.branch 303
 (.branch 302
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))
 (.branch 356
 (.branch 330
 (.branch 317
 (.branch 311
 (.branch 308
 (.leaf (.quota 1))
 (.branch 309
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 323
 (.leaf (.quota 1))
 (.branch 326
 (.leaf (.quota 1))
 (.branch 328
 (.branch 327
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 343
 (.branch 336
 (.leaf (.quota 1))
 (.branch 339
 (.branch 337
 (.leaf (.quota 1))
 (.branch 338
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 341
 (.branch 340
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 349
 (.branch 346
 (.branch 344
 (.leaf (.quota 2))
 (.branch 345
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 347
 (.leaf (.quota 2))
 (.branch 348
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 381
 (.branch 368
 (.branch 362
 (.branch 359
 (.leaf (.quota 1))
 (.branch 360
 (.leaf (.quota 2))
 (.branch 361
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1)))
 (.branch 374
 (.branch 371
 (.branch 369
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 394
 (.branch 387
 (.branch 384
 (.leaf (.quota 1))
 (.branch 385
 (.leaf (.quota 1))
 (.branch 386
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 390
 (.branch 388
 (.leaf (.quota 1))
 (.branch 389
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 400
 (.branch 397
 (.leaf (.quota 1))
 (.branch 398
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 403
 (.leaf (.quota 1))
 (.branch 405
 (.branch 404
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))))))
 (.branch 611
 (.branch 509
 (.branch 458
 (.branch 432
 (.branch 419
 (.leaf (.quota 1))
 (.branch 425
 (.branch 422
 (.branch 420
 (.leaf (.quota 1))
 (.branch 421
 (.leaf (.reuse 61))
 (.leaf (.quota 2))))
 (.branch 423
 (.leaf (.quota 1))
 (.branch 424
 (.leaf (.quota 1))
 (.leaf (.reuse 63)))))
 (.branch 428
 (.leaf (.quota 1))
 (.branch 430
 (.branch 429
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 445
 (.branch 438
 (.branch 435
 (.leaf (.quota 1))
 (.branch 436
 (.leaf (.quota 2))
 (.branch 437
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 441
 (.branch 439
 (.leaf (.quota 1))
 (.branch 440
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 443
 (.leaf (.quota 1))
 (.branch 444
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 451
 (.branch 448
 (.branch 446
 (.leaf (.quota 1))
 (.branch 447
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 454
 (.branch 452
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 456
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 483
 (.branch 470
 (.leaf (.quota 1))
 (.branch 476
 (.leaf (.quota 1))
 (.branch 479
 (.leaf (.quota 1))
 (.branch 481
 (.branch 480
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))
 (.branch 496
 (.branch 489
 (.branch 486
 (.leaf (.quota 1))
 (.branch 487
 (.leaf (.quota 2))
 (.branch 488
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 492
 (.leaf (.quota 1))
 (.branch 494
 (.leaf (.quota 2))
 (.branch 495
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 502
 (.branch 499
 (.leaf (.quota 1))
 (.branch 500
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))))
 (.branch 560
 (.branch 534
 (.branch 521
 (.leaf (.quota 1))
 (.branch 527
 (.branch 524
 (.leaf (.quota 1))
 (.branch 525
 (.leaf (.quota 1))
 (.branch 526
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 530
 (.leaf (.quota 1))
 (.branch 532
 (.branch 531
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 547
 (.branch 540
 (.leaf (.quota 1))
 (.branch 543
 (.leaf (.quota 1))
 (.branch 545
 (.branch 544
 (.leaf (.quota 1))
 (.leaf (.reuse 87)))
 (.branch 546
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 553
 (.branch 550
 (.branch 548
 (.leaf (.quota 1))
 (.branch 549
 (.leaf (.reuse 89))
 (.leaf (.quota 1))))
 (.branch 551
 (.leaf (.quota 1))
 (.branch 552
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 556
 (.leaf (.quota 1))
 (.branch 558
 (.branch 557
 (.leaf (.quota 1))
 (.leaf (.reuse 91)))
 (.branch 559
 (.leaf (.reuse 92))
 (.leaf (.reuse 93))))))))
 (.branch 585
 (.branch 572
 (.branch 566
 (.branch 563
 (.branch 561
 (.leaf (.reuse 94))
 (.leaf (.quota 1)))
 (.branch 564
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 578
 (.leaf (.quota 1))
 (.branch 581
 (.branch 579
 (.leaf (.reuse 96))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 598
 (.branch 591
 (.branch 588
 (.branch 586
 (.leaf (.reuse 97))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 604
 (.branch 601
 (.branch 599
 (.leaf (.quota 1))
 (.branch 600
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 607
 (.branch 605
 (.leaf (.quota 1))
 (.branch 606
 (.leaf (.reuse 99))
 (.leaf (.quota 1))))
 (.branch 609
 (.leaf (.quota 1))
 (.branch 610
 (.leaf (.reuse 100))
 (.leaf (.quota 1))))))))))
 (.branch 713
 (.branch 662
 (.branch 636
 (.branch 623
 (.leaf (.quota 1))
 (.branch 629
 (.branch 626
 (.branch 624
 (.leaf (.quota 1))
 (.branch 625
 (.leaf (.reuse 101))
 (.leaf (.quota 2))))
 (.branch 627
 (.leaf (.quota 1))
 (.branch 628
 (.leaf (.quota 1))
 (.leaf (.reuse 103)))))
 (.leaf (.quota 1))))
 (.branch 649
 (.branch 642
 (.leaf (.quota 1))
 (.branch 645
 (.branch 643
 (.leaf (.reuse 104))
 (.leaf (.quota 1)))
 (.branch 647
 (.branch 646
 (.leaf (.quota 1))
 (.leaf (.reuse 105)))
 (.branch 648
 (.leaf (.reuse 106))
 (.leaf (.quota 1))))))
 (.branch 655
 (.branch 652
 (.branch 650
 (.leaf (.quota 1))
 (.branch 651
 (.leaf (.reuse 107))
 (.leaf (.reuse 108))))
 (.branch 653
 (.leaf (.reuse 109))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 687
 (.branch 674
 (.branch 668
 (.branch 665
 (.branch 663
 (.leaf (.quota 1))
 (.branch 664
 (.leaf (.quota 1))
 (.leaf (.reuse 112))))
 (.branch 666
 (.leaf (.reuse 113))
 (.branch 667
 (.leaf (.reuse 114))
 (.leaf (.reuse 115)))))
 (.branch 671
 (.leaf (.quota 1))
 (.branch 672
 (.leaf (.reuse 118))
 (.branch 673
 (.leaf (.reuse 119))
 (.leaf (.quota 1))))))
 (.branch 680
 (.branch 677
 (.leaf (.quota 1))
 (.branch 678
 (.leaf (.quota 1))
 (.branch 679
 (.leaf (.reuse 120))
 (.leaf (.quota 1)))))
 (.branch 683
 (.leaf (.quota 1))
 (.branch 685
 (.branch 684
 (.leaf (.quota 1))
 (.leaf (.reuse 121)))
 (.leaf (.quota 1))))))
 (.branch 700
 (.leaf (.quota 1))
 (.branch 706
 (.branch 703
 (.branch 701
 (.leaf (.quota 2))
 (.branch 702
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 709
 (.leaf (.quota 1))
 (.branch 711
 (.branch 710
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 712
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 764
 (.branch 738
 (.branch 725
 (.branch 719
 (.branch 716
 (.leaf (.quota 1))
 (.branch 717
 (.leaf (.quota 2))
 (.branch 718
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 722
 (.leaf (.quota 1))
 (.branch 723
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 731
 (.leaf (.quota 1))
 (.branch 734
 (.branch 732
 (.leaf (.quota 2))
 (.branch 733
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 736
 (.leaf (.quota 1))
 (.branch 737
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 751
 (.branch 744
 (.branch 741
 (.leaf (.quota 2))
 (.branch 742
 (.leaf (.quota 2))
 (.branch 743
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 747
 (.branch 745
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 757
 (.branch 754
 (.leaf (.quota 1))
 (.branch 755
 (.leaf (.quota 1))
 (.branch 756
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 760
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 789
 (.branch 776
 (.branch 770
 (.branch 767
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 773
 (.branch 771
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 802
 (.branch 795
 (.branch 792
 (.leaf (.quota 1))
 (.branch 793
 (.leaf (.quota 1))
 (.branch 794
 (.leaf (.quota 1))
 (.leaf (.reuse 146)))))
 (.branch 798
 (.leaf (.quota 1))
 (.branch 800
 (.leaf (.quota 1))
 (.branch 801
 (.leaf (.quota 1))
 (.leaf (.reuse 147))))))
 (.branch 808
 (.leaf (.quota 1))
 (.branch 811
 (.leaf (.quota 1))
 (.branch 813
 (.leaf (.quota 1))
 (.branch 814
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))))))
 (.branch 1223
 (.branch 1019
 (.branch 917
 (.branch 866
 (.branch 840
 (.branch 827
 (.branch 821
 (.branch 818
 (.branch 816
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 833
 (.leaf (.quota 1))
 (.branch 836
 (.leaf (.quota 1))
 (.branch 838
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 853
 (.branch 846
 (.branch 843
 (.branch 841
 (.leaf (.quota 1))
 (.branch 842
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 844
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 849
 (.branch 847
 (.leaf (.quota 1))
 (.branch 848
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 859
 (.branch 856
 (.branch 854
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 862
 (.branch 860
 (.leaf (.quota 1))
 (.branch 861
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 891
 (.branch 878
 (.branch 872
 (.branch 869
 (.branch 867
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 870
 (.leaf (.quota 2))
 (.branch 871
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 875
 (.branch 873
 (.leaf (.quota 1))
 (.branch 874
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 884
 (.branch 881
 (.branch 879
 (.leaf (.quota 1))
 (.branch 880
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 887
 (.leaf (.quota 1))
 (.branch 889
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 904
 (.branch 897
 (.branch 894
 (.branch 892
 (.leaf (.quota 1))
 (.branch 893
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 895
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 900
 (.leaf (.quota 1))
 (.branch 902
 (.branch 901
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 903
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 910
 (.branch 907
 (.leaf (.quota 1))
 (.branch 908
 (.leaf (.quota 2))
 (.branch 909
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 913
 (.branch 911
 (.leaf (.quota 1))
 (.branch 912
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 915
 (.leaf (.quota 1))
 (.branch 916
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 968
 (.branch 942
 (.branch 929
 (.branch 923
 (.branch 920
 (.branch 918
 (.leaf (.quota 2))
 (.branch 919
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 926
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 935
 (.leaf (.quota 1))
 (.branch 938
 (.branch 936
 (.leaf (.quota 2))
 (.branch 937
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 955
 (.branch 948
 (.leaf (.quota 1))
 (.branch 951
 (.leaf (.quota 1))
 (.branch 953
 (.branch 952
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 954
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 961
 (.leaf (.quota 1))
 (.branch 964
 (.branch 962
 (.leaf (.quota 1))
 (.branch 963
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 993
 (.branch 980
 (.branch 974
 (.branch 971
 (.leaf (.quota 2))
 (.branch 972
 (.leaf (.quota 2))
 (.branch 973
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1006
 (.branch 999
 (.branch 996
 (.branch 994
 (.leaf (.quota 1))
 (.branch 995
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1002
 (.leaf (.quota 2))
 (.branch 1004
 (.branch 1003
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1012
 (.leaf (.quota 1))
 (.branch 1015
 (.leaf (.quota 1))
 (.branch 1017
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 1121
 (.branch 1070
 (.branch 1044
 (.branch 1031
 (.branch 1025
 (.leaf (.quota 1))
 (.branch 1028
 (.branch 1026
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1037
 (.branch 1034
 (.branch 1032
 (.leaf (.quota 1))
 (.branch 1033
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1035
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1040
 (.branch 1038
 (.leaf (.quota 1))
 (.branch 1039
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1042
 (.branch 1041
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1057
 (.branch 1050
 (.branch 1047
 (.branch 1045
 (.leaf (.quota 1))
 (.branch 1046
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1048
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1095
 (.branch 1082
 (.leaf (.quota 1))
 (.branch 1088
 (.branch 1085
 (.branch 1083
 (.leaf (.quota 1))
 (.branch 1084
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1091
 (.branch 1089
 (.leaf (.quota 1))
 (.branch 1090
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1093
 (.leaf (.quota 1))
 (.branch 1094
 (.leaf (.quota 1))
 (.leaf (.reuse 227)))))))
 (.branch 1108
 (.branch 1101
 (.branch 1098
 (.branch 1096
 (.leaf (.quota 1))
 (.branch 1097
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1099
 (.leaf (.quota 2))
 (.branch 1100
 (.leaf (.quota 1))
 (.leaf (.reuse 230)))))
 (.branch 1104
 (.branch 1102
 (.leaf (.quota 1))
 (.branch 1103
 (.leaf (.reuse 231))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 1114
 (.branch 1111
 (.branch 1109
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1172
 (.branch 1146
 (.branch 1133
 (.leaf (.quota 1))
 (.branch 1139
 (.branch 1136
 (.branch 1134
 (.leaf (.quota 1))
 (.branch 1135
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 1142
 (.branch 1140
 (.leaf (.quota 1))
 (.branch 1141
 (.leaf (.quota 1))
 (.leaf (.reuse 236))))
 (.branch 1144
 (.branch 1143
 (.leaf (.reuse 237))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))
 (.branch 1159
 (.branch 1152
 (.branch 1149
 (.branch 1147
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1155
 (.leaf (.quota 1))
 (.branch 1157
 (.branch 1156
 (.leaf (.quota 1))
 (.leaf (.reuse 241)))
 (.branch 1158
 (.leaf (.reuse 242))
 (.leaf (.reuse 243))))))
 (.branch 1165
 (.branch 1162
 (.branch 1160
 (.leaf (.reuse 244))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1168
 (.leaf (.quota 1))
 (.branch 1170
 (.branch 1169
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1171
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 1197
 (.branch 1184
 (.branch 1178
 (.leaf (.quota 1))
 (.branch 1181
 (.branch 1179
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 1190
 (.branch 1187
 (.branch 1185
 (.leaf (.quota 1))
 (.branch 1186
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1188
 (.leaf (.quota 1))
 (.branch 1189
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1))))
 (.branch 1210
 (.branch 1203
 (.branch 1200
 (.leaf (.quota 1))
 (.branch 1201
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1216
 (.branch 1213
 (.leaf (.quota 1))
 (.branch 1214
 (.leaf (.quota 1))
 (.branch 1215
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1219
 (.leaf (.quota 1))
 (.branch 1221
 (.leaf (.quota 1))
 (.branch 1222
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))))
 (.branch 1427
 (.branch 1325
 (.branch 1274
 (.branch 1248
 (.branch 1235
 (.leaf (.quota 1))
 (.branch 1241
 (.branch 1238
 (.branch 1236
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1244
 (.leaf (.quota 1))
 (.branch 1246
 (.branch 1245
 (.leaf (.reuse 257))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1261
 (.branch 1254
 (.leaf (.quota 1))
 (.branch 1257
 (.branch 1255
 (.leaf (.reuse 258))
 (.branch 1256
 (.leaf (.reuse 259))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 1299
 (.branch 1286
 (.branch 1280
 (.branch 1277
 (.leaf (.quota 1))
 (.branch 1278
 (.leaf (.quota 1))
 (.branch 1279
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1283
 (.leaf (.quota 1))
 (.branch 1284
 (.leaf (.quota 2))
 (.branch 1285
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 1292
 (.branch 1289
 (.leaf (.quota 1))
 (.branch 1290
 (.leaf (.quota 2))
 (.branch 1291
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 1312
 (.branch 1305
 (.leaf (.quota 1))
 (.branch 1308
 (.leaf (.quota 1))
 (.branch 1310
 (.leaf (.quota 1))
 (.branch 1311
 (.leaf (.reuse 266))
 (.leaf (.quota 1))))))
 (.branch 1318
 (.leaf (.quota 1))
 (.branch 1321
 (.leaf (.quota 1))
 (.branch 1323
 (.branch 1322
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1324
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 1376
 (.branch 1350
 (.branch 1337
 (.branch 1331
 (.leaf (.quota 1))
 (.branch 1334
 (.branch 1332
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1335
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1343
 (.leaf (.quota 1))
 (.branch 1346
 (.leaf (.quota 1))
 (.branch 1348
 (.branch 1347
 (.leaf (.quota 1))
 (.leaf (.reuse 273)))
 (.branch 1349
 (.leaf (.reuse 274))
 (.leaf (.reuse 275)))))))
 (.branch 1363
 (.branch 1356
 (.branch 1353
 (.branch 1351
 (.leaf (.reuse 276))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1359
 (.leaf (.quota 1))
 (.branch 1361
 (.leaf (.quota 1))
 (.branch 1362
 (.leaf (.reuse 280))
 (.leaf (.reuse 281))))))
 (.branch 1369
 (.branch 1366
 (.branch 1364
 (.leaf (.reuse 282))
 (.leaf (.quota 1)))
 (.branch 1367
 (.leaf (.quota 1))
 (.branch 1368
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1372
 (.branch 1370
 (.leaf (.reuse 284))
 (.branch 1371
 (.leaf (.reuse 285))
 (.leaf (.quota 1))))
 (.branch 1374
 (.branch 1373
 (.leaf (.quota 1))
 (.leaf (.reuse 286)))
 (.branch 1375
 (.leaf (.reuse 287))
 (.leaf (.quota 1))))))))
 (.branch 1401
 (.branch 1388
 (.branch 1382
 (.branch 1379
 (.leaf (.quota 1))
 (.branch 1380
 (.leaf (.reuse 290))
 (.branch 1381
 (.leaf (.reuse 291))
 (.leaf (.quota 1)))))
 (.branch 1385
 (.leaf (.quota 1))
 (.branch 1386
 (.leaf (.quota 1))
 (.branch 1387
 (.leaf (.reuse 292))
 (.leaf (.reuse 293))))))
 (.branch 1394
 (.branch 1391
 (.branch 1389
 (.leaf (.reuse 294))
 (.branch 1390
 (.leaf (.reuse 295))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1397
 (.branch 1395
 (.leaf (.reuse 298))
 (.branch 1396
 (.leaf (.reuse 299))
 (.leaf (.reuse 300))))
 (.branch 1399
 (.branch 1398
 (.leaf (.reuse 301))
 (.leaf (.reuse 302)))
 (.branch 1400
 (.leaf (.quota 1))
 (.leaf (.reuse 304)))))))
 (.branch 1414
 (.branch 1407
 (.leaf (.quota 1))
 (.branch 1410
 (.branch 1408
 (.leaf (.quota 1))
 (.branch 1409
 (.leaf (.reuse 305))
 (.leaf (.reuse 306))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 1529
 (.branch 1478
 (.branch 1452
 (.branch 1439
 (.branch 1433
 (.leaf (.quota 1))
 (.branch 1436
 (.leaf (.quota 1))
 (.branch 1437
 (.leaf (.quota 1))
 (.branch 1438
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1445
 (.branch 1442
 (.branch 1440
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1443
 (.leaf (.quota 1))
 (.branch 1444
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1448
 (.leaf (.quota 1))
 (.branch 1450
 (.branch 1449
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1465
 (.branch 1458
 (.leaf (.quota 1))
 (.branch 1461
 (.branch 1459
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 1503
 (.branch 1490
 (.leaf (.quota 1))
 (.branch 1496
 (.branch 1493
 (.leaf (.quota 1))
 (.branch 1494
 (.leaf (.quota 1))
 (.branch 1495
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 1499
 (.leaf (.quota 1))
 (.branch 1501
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1516
 (.branch 1509
 (.leaf (.quota 1))
 (.branch 1512
 (.leaf (.quota 1))
 (.branch 1514
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1522
 (.branch 1519
 (.branch 1517
 (.leaf (.quota 1))
 (.branch 1518
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1520
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 1580
 (.branch 1554
 (.branch 1541
 (.branch 1535
 (.branch 1532
 (.leaf (.quota 1))
 (.branch 1533
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1547
 (.leaf (.quota 1))
 (.branch 1550
 (.branch 1548
 (.leaf (.quota 1))
 (.branch 1549
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 1552
 (.branch 1551
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))
 (.branch 1567
 (.branch 1560
 (.branch 1557
 (.branch 1555
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1558
 (.leaf (.quota 2))
 (.branch 1559
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 1563
 (.leaf (.quota 2))
 (.branch 1565
 (.leaf (.quota 2))
 (.branch 1566
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 1573
 (.branch 1570
 (.branch 1568
 (.leaf (.quota 2))
 (.branch 1569
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1571
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 1605
 (.branch 1592
 (.leaf (.quota 1))
 (.branch 1598
 (.branch 1595
 (.leaf (.quota 1))
 (.branch 1596
 (.leaf (.quota 1))
 (.branch 1597
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1))))
 (.branch 1618
 (.branch 1611
 (.branch 1608
 (.branch 1606
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1609
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1624
 (.branch 1621
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 1627
 (.branch 1625
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 1629
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0364.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0364.rawLeaves 350 (RootedForests.RootedSubsumedForest0708.rawLeaves i) (routes.get i)

def disposition (j : Fin 1631) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0364.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0364
