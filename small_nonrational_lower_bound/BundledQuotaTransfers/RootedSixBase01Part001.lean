module
prelude
public import BundledQuotaTransfers.RootedSixBase01Part000
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0340Dispositions
public import RootedSubsumedForest0344Data
public import RootedSubsumedForest0341Dispositions
public import RootedSubsumedForest0349Data
public import RootedSubsumedForest0342Dispositions
public import RootedSubsumedForest0352Data
public import RootedSubsumedForest0343Dispositions
public import RootedSubsumedForest0345Dispositions
public import RootedSubsumedForest0346Dispositions
public import RootedSubsumedForest0354Data
public import RootedSubsumedForest0347Dispositions
public import RootedSubsumedForest0348Dispositions
public import RootedSubsumedForest0355Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0311Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0311
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0311

/- Original module: RootedQuotaTransfer0311Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0311
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0311

/- Original module: RootedQuotaTransfer0311. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0311
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 192 :=
  (interval_append routeTest 0 128 192
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 192) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0311.quota
      ((RootedForests.RootedSubsumedForest0320.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0311.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0311.rawLeaves 42 RootedForests.RootedSubsumedForest0311.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0311.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0320.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0311

/- Original module: RootedQuotaTransfer0340Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0340
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 340: use the complete forest for case 344, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0340.quota k ≤ RootedForests.RootedSubsumedForest0344.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0340.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0340.rawLeaves 1 (RootedForests.RootedSubsumedForest0344.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0340.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0340

/- Original module: RootedQuotaTransfer0340Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0340
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0340

/- Original module: RootedQuotaTransfer0340. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0340
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0340.quota
      ((RootedForests.RootedSubsumedForest0344.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0340.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0340.rawLeaves 1 RootedForests.RootedSubsumedForest0340.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0340.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0344.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0340

/- Original module: RootedQuotaTransfer0341Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0341
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 341: use the complete forest for case 349, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0341.quota k ≤ RootedForests.RootedSubsumedForest0349.quota k := by
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
(.leaf (.quota 1))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0341.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0341.rawLeaves 1 (RootedForests.RootedSubsumedForest0349.rawLeaves i) (routes.get i)

def disposition (j : Fin 5) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0341.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0341

/- Original module: RootedQuotaTransfer0341Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0341
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 5 :=
  interval_of_check test0 0 5 (by decide +kernel)

theorem test0_complete : Interval test0 0 5 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 5 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0341

/- Original module: RootedQuotaTransfer0341. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0341
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 5 :=
  routeInterval0

theorem disposition_checked (j : Fin 5) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0341.quota
      ((RootedForests.RootedSubsumedForest0349.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0341.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0341.rawLeaves 1 RootedForests.RootedSubsumedForest0341.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0341.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0349.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0341

/- Original module: RootedQuotaTransfer0342Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0342
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 342: use the complete forest for case 352, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0342.quota k ≤ RootedForests.RootedSubsumedForest0352.quota k := by
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
(.branch 76
 (.branch 38
 (.leaf (.quota 1))
 (.branch 57
 (.branch 47
 (.leaf (.quota 1))
 (.branch 52
 (.branch 49
 (.leaf (.quota 1))
 (.branch 50
 (.leaf (.quota 1))
 (.branch 51
 (.leaf (.quota 1))
 (.leaf (.reuse 0)))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0342.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0342.rawLeaves 1 (RootedForests.RootedSubsumedForest0352.rawLeaves i) (routes.get i)

def disposition (j : Fin 152) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0342.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0342

/- Original module: RootedQuotaTransfer0342Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0342
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0342

/- Original module: RootedQuotaTransfer0342Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0342
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 24 :=
  interval_of_check test128 16 8 (by decide +kernel)

theorem test128_complete : Interval test128 0 24 :=
  (interval_append test128 0 16 24
  test128_block_0
  test128_block_1)
theorem routeInterval128 : Interval routeTest 128 152 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0342

/- Original module: RootedQuotaTransfer0342. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0342
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 152 :=
  (interval_append routeTest 0 128 152
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 152) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0342.quota
      ((RootedForests.RootedSubsumedForest0352.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0342.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0342.rawLeaves 1 RootedForests.RootedSubsumedForest0342.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0342.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0352.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0342

/- Original module: RootedQuotaTransfer0343Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0343
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 343: use the complete forest for case 349, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0343.quota k ≤ RootedForests.RootedSubsumedForest0349.quota k := by
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
(.branch 2
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.reuse 0)))
 (.branch 3
 (.leaf (.reuse 1))
 (.branch 4
 (.leaf (.reuse 2))
 (.leaf (.reuse 3)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0343.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0343.rawLeaves 4 (RootedForests.RootedSubsumedForest0349.rawLeaves i) (routes.get i)

def disposition (j : Fin 5) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0343.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0343

/- Original module: RootedQuotaTransfer0343Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0343
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 5 :=
  interval_of_check test0 0 5 (by decide +kernel)

theorem test0_complete : Interval test0 0 5 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 5 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0343

/- Original module: RootedQuotaTransfer0343. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0343
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 5 :=
  routeInterval0

theorem disposition_checked (j : Fin 5) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0343.quota
      ((RootedForests.RootedSubsumedForest0349.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0343.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0343.rawLeaves 4 RootedForests.RootedSubsumedForest0343.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0343.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0349.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0343

/- Original module: RootedQuotaTransfer0345Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0345
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 345: use the complete forest for case 349, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0345.quota k ≤ RootedForests.RootedSubsumedForest0349.quota k := by
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
(.leaf (.quota 1))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0345.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0345.rawLeaves 1 (RootedForests.RootedSubsumedForest0349.rawLeaves i) (routes.get i)

def disposition (j : Fin 5) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0345.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0345

/- Original module: RootedQuotaTransfer0345Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0345
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 5 :=
  interval_of_check test0 0 5 (by decide +kernel)

theorem test0_complete : Interval test0 0 5 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 5 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0345

/- Original module: RootedQuotaTransfer0345. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0345
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 5 :=
  routeInterval0

theorem disposition_checked (j : Fin 5) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0345.quota
      ((RootedForests.RootedSubsumedForest0349.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0345.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0345.rawLeaves 1 RootedForests.RootedSubsumedForest0345.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0345.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0349.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0345

/- Original module: RootedQuotaTransfer0346Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0346
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 346: use the complete forest for case 354, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0346.quota k ≤ RootedForests.RootedSubsumedForest0354.quota k := by
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
(.leaf (.quota 1))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0346.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0346.rawLeaves 1 (RootedForests.RootedSubsumedForest0354.rawLeaves i) (routes.get i)

def disposition (j : Fin 156) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0346.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0346

/- Original module: RootedQuotaTransfer0346Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0346
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0346

/- Original module: RootedQuotaTransfer0346Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0346
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0346

/- Original module: RootedQuotaTransfer0346. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0346
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 156 :=
  (interval_append routeTest 0 128 156
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 156) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0346.quota
      ((RootedForests.RootedSubsumedForest0354.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0346.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0346.rawLeaves 1 RootedForests.RootedSubsumedForest0346.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0346.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0354.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0346

/- Original module: RootedQuotaTransfer0347Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0347
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 347: use the complete forest for case 352, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0347.quota k ≤ RootedForests.RootedSubsumedForest0352.quota k := by
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
(.branch 76
 (.branch 38
 (.branch 19
 (.branch 9
 (.branch 4
 (.leaf (.quota 1))
 (.branch 6
 (.branch 5
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 28
 (.leaf (.quota 1))
 (.branch 33
 (.leaf (.quota 1))
 (.branch 35
 (.leaf (.quota 1))
 (.branch 36
 (.leaf (.reuse 1))
 (.leaf (.quota 1)))))))
 (.branch 57
 (.branch 47
 (.branch 42
 (.branch 40
 (.leaf (.quota 1))
 (.branch 41
 (.leaf (.reuse 2))
 (.leaf (.reuse 3))))
 (.branch 44
 (.branch 43
 (.leaf (.reuse 4))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf (.reuse 5))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 66
 (.leaf (.quota 1))
 (.branch 71
 (.leaf (.quota 1))
 (.branch 73
 (.leaf (.quota 1))
 (.branch 74
 (.leaf (.quota 1))
 (.branch 75
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 114
 (.branch 95
 (.branch 85
 (.branch 80
 (.branch 78
 (.leaf (.quota 1))
 (.branch 79
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 90
 (.leaf (.quota 1))
 (.branch 92
 (.branch 91
 (.leaf (.quota 1))
 (.leaf (.reuse 9)))
 (.leaf (.quota 1)))))
 (.branch 104
 (.branch 99
 (.leaf (.quota 1))
 (.branch 101
 (.branch 100
 (.leaf (.quota 1))
 (.leaf (.reuse 10)))
 (.leaf (.quota 1))))
 (.branch 109
 (.branch 106
 (.branch 105
 (.leaf (.quota 1))
 (.leaf (.reuse 11)))
 (.branch 107
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 111
 (.branch 110
 (.leaf (.reuse 13))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 133
 (.branch 123
 (.branch 118
 (.leaf (.quota 1))
 (.branch 120
 (.branch 119
 (.leaf (.quota 1))
 (.leaf (.reuse 14)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0347.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0347.rawLeaves 15 (RootedForests.RootedSubsumedForest0352.rawLeaves i) (routes.get i)

def disposition (j : Fin 152) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0347.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0347

/- Original module: RootedQuotaTransfer0347Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0347
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0347

/- Original module: RootedQuotaTransfer0347Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0347
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 24 :=
  interval_of_check test128 16 8 (by decide +kernel)

theorem test128_complete : Interval test128 0 24 :=
  (interval_append test128 0 16 24
  test128_block_0
  test128_block_1)
theorem routeInterval128 : Interval routeTest 128 152 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0347

/- Original module: RootedQuotaTransfer0347. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0347
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 152 :=
  (interval_append routeTest 0 128 152
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 152) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0347.quota
      ((RootedForests.RootedSubsumedForest0352.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0347.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0347.rawLeaves 15 RootedForests.RootedSubsumedForest0347.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0347.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0352.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0347

/- Original module: RootedQuotaTransfer0348Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0348
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 348: use the complete forest for case 355, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0348.quota k ≤ RootedForests.RootedSubsumedForest0355.quota k := by
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
 (.leaf (.quota 1))
 (.branch 191
 (.branch 159
 (.leaf (.quota 1))
 (.branch 175
 (.branch 167
 (.branch 163
 (.leaf (.quota 1))
 (.branch 165
 (.branch 164
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 223
 (.branch 207
 (.branch 199
 (.leaf (.quota 1))
 (.branch 203
 (.branch 201
 (.leaf (.quota 1))
 (.branch 202
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 215
 (.leaf (.quota 1))
 (.branch 219
 (.branch 217
 (.leaf (.quota 1))
 (.branch 218
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 382
 (.branch 318
 (.branch 286
 (.branch 270
 (.leaf (.quota 1))
 (.branch 278
 (.leaf (.quota 1))
 (.branch 282
 (.leaf (.quota 1))
 (.branch 284
 (.leaf (.quota 1))
 (.branch 285
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.leaf (.quota 1)))
 (.branch 350
 (.branch 334
 (.branch 326
 (.branch 322
 (.branch 320
 (.leaf (.quota 1))
 (.branch 321
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 446
 (.branch 414
 (.leaf (.quota 1))
 (.branch 430
 (.leaf (.quota 1))
 (.branch 438
 (.leaf (.quota 1))
 (.branch 442
 (.branch 440
 (.branch 439
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))))
 (.branch 765
 (.leaf (.quota 1))
 (.branch 893
 (.leaf (.quota 1))
 (.branch 957
 (.leaf (.quota 1))
 (.branch 989
 (.leaf (.quota 1))
 (.branch 1005
 (.branch 997
 (.branch 993
 (.branch 991
 (.branch 990
 (.leaf (.reuse 6))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))
 (.branch 1531
 (.branch 1276
 (.branch 1148
 (.branch 1084
 (.leaf (.quota 1))
 (.branch 1116
 (.branch 1100
 (.branch 1092
 (.leaf (.quota 1))
 (.branch 1096
 (.leaf (.quota 1))
 (.branch 1098
 (.leaf (.quota 1))
 (.branch 1099
 (.leaf (.quota 1))
 (.leaf (.reuse 7))))))
 (.branch 1108
 (.branch 1104
 (.leaf (.quota 1))
 (.branch 1106
 (.leaf (.quota 1))
 (.branch 1107
 (.leaf (.quota 1))
 (.leaf (.reuse 8)))))
 (.branch 1112
 (.branch 1110
 (.branch 1109
 (.leaf (.reuse 9))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1132
 (.branch 1124
 (.leaf (.quota 1))
 (.branch 1128
 (.leaf (.quota 1))
 (.branch 1130
 (.branch 1129
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 1212
 (.leaf (.quota 1))
 (.branch 1244
 (.branch 1228
 (.branch 1220
 (.leaf (.quota 1))
 (.branch 1224
 (.leaf (.quota 1))
 (.branch 1226
 (.branch 1225
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1403
 (.leaf (.quota 1))
 (.branch 1467
 (.leaf (.quota 1))
 (.branch 1499
 (.leaf (.quota 1))
 (.branch 1515
 (.branch 1507
 (.branch 1503
 (.leaf (.quota 1))
 (.branch 1505
 (.branch 1504
 (.leaf (.quota 1))
 (.leaf (.reuse 12)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1523
 (.branch 1519
 (.branch 1517
 (.branch 1516
 (.leaf (.quota 1))
 (.leaf (.reuse 13)))
 (.leaf (.quota 1)))
 (.branch 1521
 (.branch 1520
 (.leaf (.quota 1))
 (.leaf (.reuse 14)))
 (.leaf (.quota 1))))
 (.branch 1527
 (.branch 1525
 (.branch 1524
 (.leaf (.reuse 15))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))))
 (.branch 1786
 (.branch 1658
 (.branch 1594
 (.branch 1562
 (.branch 1546
 (.branch 1538
 (.branch 1534
 (.leaf (.quota 1))
 (.branch 1536
 (.branch 1535
 (.leaf (.quota 1))
 (.leaf (.reuse 16)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1578
 (.branch 1570
 (.branch 1566
 (.branch 1564
 (.leaf (.quota 1))
 (.branch 1565
 (.leaf (.quota 1))
 (.leaf (.reuse 17))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1586
 (.branch 1582
 (.leaf (.quota 1))
 (.branch 1584
 (.branch 1583
 (.leaf (.quota 1))
 (.leaf (.reuse 18)))
 (.leaf (.quota 1))))
 (.branch 1590
 (.branch 1588
 (.branch 1587
 (.leaf (.quota 1))
 (.leaf (.reuse 19)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1626
 (.branch 1610
 (.branch 1602
 (.leaf (.quota 1))
 (.branch 1606
 (.branch 1604
 (.leaf (.quota 1))
 (.branch 1605
 (.leaf (.reuse 20))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1722
 (.branch 1690
 (.branch 1674
 (.leaf (.quota 1))
 (.branch 1682
 (.branch 1678
 (.branch 1676
 (.leaf (.quota 1))
 (.branch 1677
 (.leaf (.reuse 21))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1914
 (.leaf (.quota 1))
 (.branch 1978
 (.branch 1946
 (.branch 1930
 (.branch 1922
 (.leaf (.quota 1))
 (.branch 1926
 (.leaf (.quota 1))
 (.branch 1928
 (.branch 1927
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2010
 (.leaf (.quota 1))
 (.branch 2026
 (.leaf (.quota 1))
 (.branch 2034
 (.branch 2030
 (.branch 2028
 (.branch 2027
 (.leaf (.quota 1))
 (.leaf (.reuse 23)))
 (.branch 2029
 (.leaf (.reuse 24))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))))
 (.branch 3063
 (.branch 2552
 (.branch 2297
 (.branch 2169
 (.branch 2105
 (.branch 2073
 (.leaf (.quota 1))
 (.branch 2089
 (.branch 2081
 (.leaf (.quota 1))
 (.branch 2085
 (.branch 2083
 (.branch 2082
 (.leaf (.quota 1))
 (.leaf (.reuse 25)))
 (.leaf (.quota 1)))
 (.branch 2087
 (.branch 2086
 (.leaf (.reuse 26))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 2137
 (.branch 2121
 (.leaf (.quota 1))
 (.branch 2129
 (.branch 2125
 (.leaf (.quota 1))
 (.branch 2127
 (.leaf (.quota 1))
 (.branch 2128
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 2153
 (.branch 2145
 (.leaf (.quota 1))
 (.branch 2149
 (.branch 2147
 (.leaf (.quota 1))
 (.branch 2148
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 2233
 (.leaf (.quota 1))
 (.branch 2265
 (.branch 2249
 (.branch 2241
 (.branch 2237
 (.leaf (.quota 1))
 (.branch 2239
 (.leaf (.quota 1))
 (.branch 2240
 (.leaf (.reuse 29))
 (.leaf (.quota 1)))))
 (.branch 2245
 (.branch 2243
 (.leaf (.quota 1))
 (.branch 2244
 (.leaf (.reuse 30))
 (.leaf (.quota 1))))
 (.branch 2247
 (.branch 2246
 (.leaf (.reuse 31))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2257
 (.branch 2253
 (.branch 2251
 (.leaf (.quota 1))
 (.branch 2252
 (.leaf (.quota 1))
 (.leaf (.reuse 32))))
 (.leaf (.quota 1)))
 (.branch 2261
 (.leaf (.quota 1))
 (.branch 2263
 (.leaf (.quota 1))
 (.branch 2264
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.leaf (.quota 1)))))
 (.branch 2424
 (.branch 2360
 (.branch 2328
 (.branch 2312
 (.leaf (.quota 1))
 (.branch 2320
 (.leaf (.quota 1))
 (.branch 2324
 (.branch 2322
 (.branch 2321
 (.leaf (.reuse 34))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2344
 (.branch 2336
 (.leaf (.quota 1))
 (.branch 2340
 (.branch 2338
 (.branch 2337
 (.leaf (.reuse 35))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2342
 (.leaf (.quota 1))
 (.branch 2343
 (.leaf (.reuse 36))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1))))
 (.branch 2392
 (.branch 2376
 (.branch 2368
 (.leaf (.quota 1))
 (.branch 2372
 (.leaf (.quota 1))
 (.branch 2374
 (.leaf (.quota 1))
 (.branch 2375
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 2384
 (.branch 2380
 (.branch 2378
 (.leaf (.quota 1))
 (.branch 2379
 (.leaf (.quota 1))
 (.leaf (.reuse 38))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 2488
 (.branch 2456
 (.branch 2440
 (.leaf (.quota 1))
 (.branch 2448
 (.branch 2444
 (.branch 2442
 (.branch 2441
 (.leaf (.quota 1))
 (.leaf (.reuse 39)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2472
 (.leaf (.quota 1))
 (.branch 2480
 (.branch 2476
 (.branch 2474
 (.leaf (.quota 1))
 (.branch 2475
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2520
 (.branch 2504
 (.leaf (.quota 1))
 (.branch 2512
 (.branch 2508
 (.branch 2506
 (.leaf (.quota 1))
 (.branch 2507
 (.leaf (.reuse 42))
 (.leaf (.reuse 43))))
 (.leaf (.quota 1)))
 (.branch 2516
 (.branch 2514
 (.branch 2513
 (.leaf (.quota 1))
 (.leaf (.reuse 44)))
 (.leaf (.quota 1)))
 (.branch 2518
 (.leaf (.quota 1))
 (.branch 2519
 (.leaf (.quota 1))
 (.leaf (.reuse 45)))))))
 (.leaf (.quota 1))))))
 (.branch 2807
 (.branch 2679
 (.branch 2615
 (.branch 2583
 (.branch 2567
 (.branch 2559
 (.branch 2555
 (.branch 2553
 (.leaf (.quota 1))
 (.branch 2554
 (.leaf (.reuse 46))
 (.leaf (.quota 1))))
 (.branch 2557
 (.leaf (.quota 1))
 (.branch 2558
 (.leaf (.quota 1))
 (.leaf (.reuse 47)))))
 (.leaf (.quota 1)))
 (.branch 2575
 (.leaf (.quota 1))
 (.branch 2579
 (.branch 2577
 (.branch 2576
 (.leaf (.reuse 48))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2599
 (.branch 2591
 (.leaf (.quota 1))
 (.branch 2595
 (.branch 2593
 (.leaf (.quota 1))
 (.branch 2594
 (.leaf (.reuse 49))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 2607
 (.leaf (.quota 1))
 (.branch 2611
 (.leaf (.quota 1))
 (.branch 2613
 (.branch 2612
 (.leaf (.quota 1))
 (.leaf (.reuse 50)))
 (.leaf (.quota 1)))))))
 (.branch 2647
 (.branch 2631
 (.branch 2623
 (.leaf (.quota 1))
 (.branch 2627
 (.branch 2625
 (.branch 2624
 (.leaf (.reuse 51))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2663
 (.leaf (.quota 1))
 (.branch 2671
 (.branch 2667
 (.leaf (.quota 1))
 (.branch 2669
 (.leaf (.quota 1))
 (.branch 2670
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1))))))
 (.branch 2743
 (.branch 2711
 (.leaf (.quota 1))
 (.branch 2727
 (.branch 2719
 (.branch 2715
 (.leaf (.quota 1))
 (.branch 2717
 (.branch 2716
 (.leaf (.reuse 53))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2735
 (.branch 2731
 (.branch 2729
 (.leaf (.quota 1))
 (.branch 2730
 (.leaf (.quota 1))
 (.leaf (.reuse 55))))
 (.branch 2733
 (.leaf (.quota 1))
 (.branch 2734
 (.leaf (.reuse 56))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 2775
 (.branch 2759
 (.branch 2751
 (.branch 2747
 (.branch 2745
 (.leaf (.quota 1))
 (.branch 2746
 (.leaf (.reuse 57))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 2755
 (.branch 2753
 (.leaf (.quota 1))
 (.branch 2754
 (.leaf (.reuse 58))
 (.leaf (.reuse 59))))
 (.branch 2757
 (.leaf (.quota 1))
 (.branch 2758
 (.leaf (.quota 1))
 (.leaf (.reuse 60))))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2935
 (.leaf (.quota 1))
 (.branch 2999
 (.leaf (.quota 1))
 (.branch 3031
 (.branch 3015
 (.leaf (.quota 1))
 (.branch 3023
 (.leaf (.quota 1))
 (.branch 3027
 (.leaf (.quota 1))
 (.branch 3029
 (.branch 3028
 (.leaf (.quota 1))
 (.leaf (.reuse 61)))
 (.leaf (.quota 1))))))
 (.branch 3047
 (.branch 3039
 (.leaf (.quota 1))
 (.branch 3043
 (.leaf (.quota 1))
 (.branch 3045
 (.branch 3044
 (.leaf (.quota 1))
 (.leaf (.reuse 62)))
 (.leaf (.quota 1)))))
 (.branch 3055
 (.branch 3051
 (.branch 3049
 (.leaf (.quota 1))
 (.branch 3050
 (.leaf (.quota 1))
 (.leaf (.reuse 63))))
 (.leaf (.quota 1)))
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
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3076
 (.leaf (.quota 1))
 (.branch 3077
 (.leaf (.reuse 65))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))
 (.branch 3110
 (.branch 3102
 (.leaf (.quota 1))
 (.branch 3106
 (.branch 3104
 (.branch 3103
 (.leaf (.quota 1))
 (.leaf (.reuse 66)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 3158
 (.branch 3142
 (.leaf (.quota 1))
 (.branch 3150
 (.leaf (.quota 1))
 (.branch 3154
 (.branch 3152
 (.branch 3151
 (.leaf (.reuse 67))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 3174
 (.branch 3166
 (.branch 3162
 (.leaf (.quota 1))
 (.branch 3164
 (.branch 3163
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 3254
 (.leaf (.quota 1))
 (.branch 3286
 (.branch 3270
 (.branch 3262
 (.branch 3258
 (.leaf (.quota 1))
 (.branch 3260
 (.branch 3259
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 3445
 (.leaf (.quota 1))
 (.branch 3509
 (.branch 3477
 (.leaf (.quota 1))
 (.branch 3493
 (.leaf (.quota 1))
 (.branch 3501
 (.branch 3497
 (.leaf (.quota 1))
 (.branch 3499
 (.leaf (.quota 1))
 (.branch 3500
 (.leaf (.reuse 70))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 3541
 (.branch 3525
 (.branch 3517
 (.branch 3513
 (.leaf (.quota 1))
 (.branch 3515
 (.leaf (.quota 1))
 (.branch 3516
 (.leaf (.reuse 71))
 (.leaf (.reuse 72)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3557
 (.branch 3549
 (.branch 3545
 (.branch 3543
 (.leaf (.quota 1))
 (.branch 3544
 (.leaf (.quota 1))
 (.leaf (.reuse 73))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 3828
 (.branch 3700
 (.branch 3636
 (.leaf (.quota 1))
 (.branch 3668
 (.branch 3652
 (.branch 3644
 (.branch 3640
 (.branch 3638
 (.leaf (.quota 1))
 (.branch 3639
 (.leaf (.reuse 74))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3684
 (.branch 3676
 (.branch 3672
 (.leaf (.quota 1))
 (.branch 3674
 (.branch 3673
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 3764
 (.branch 3732
 (.branch 3716
 (.branch 3708
 (.branch 3704
 (.branch 3702
 (.branch 3701
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3748
 (.branch 3740
 (.branch 3736
 (.branch 3734
 (.branch 3733
 (.leaf (.quota 1))
 (.leaf (.reuse 78)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 3956
 (.branch 3892
 (.leaf (.quota 1))
 (.branch 3924
 (.branch 3908
 (.branch 3900
 (.branch 3896
 (.branch 3894
 (.leaf (.quota 1))
 (.branch 3895
 (.leaf (.reuse 79))
 (.leaf (.quota 1))))
 (.branch 3898
 (.branch 3897
 (.leaf (.reuse 80))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 3916
 (.leaf (.quota 1))
 (.branch 3920
 (.branch 3918
 (.branch 3917
 (.leaf (.quota 1))
 (.leaf (.reuse 81)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 4020
 (.branch 3988
 (.branch 3972
 (.branch 3964
 (.branch 3960
 (.leaf (.quota 1))
 (.branch 3962
 (.leaf (.quota 1))
 (.branch 3963
 (.leaf (.quota 1))
 (.leaf (.reuse 83)))))
 (.branch 3968
 (.branch 3966
 (.branch 3965
 (.leaf (.quota 1))
 (.leaf (.reuse 84)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3980
 (.branch 3976
 (.branch 3974
 (.leaf (.quota 1))
 (.branch 3975
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 4004
 (.leaf (.quota 1))
 (.branch 4012
 (.branch 4008
 (.branch 4006
 (.leaf (.quota 1))
 (.branch 4007
 (.leaf (.quota 1))
 (.leaf (.reuse 86))))
 (.leaf (.quota 1)))
 (.branch 4016
 (.branch 4014
 (.leaf (.quota 1))
 (.branch 4015
 (.leaf (.reuse 87))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 4052
 (.leaf (.quota 1))
 (.branch 4068
 (.branch 4060
 (.leaf (.quota 1))
 (.branch 4064
 (.leaf (.quota 1))
 (.branch 4066
 (.leaf (.quota 1))
 (.branch 4067
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1))))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0348.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0348.rawLeaves 89 (RootedForests.RootedSubsumedForest0355.rawLeaves i) (routes.get i)

def disposition (j : Fin 4084) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0348.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0348

/- Original module: RootedQuotaTransfer0348Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0348
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0348

/- Original module: RootedQuotaTransfer0348Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0348
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0348
