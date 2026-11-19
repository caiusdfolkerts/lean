module
prelude
public import BundledQuotaTransfers.RootedSixBase00Part000
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0335Dispositions
public import RootedSubsumedForest0339Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0333Proof002. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0333
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test256 (i : Nat) := routeTest (i + 256)
theorem test256_block_0 : Interval test256 0 16 :=
  interval_of_check test256 0 16 (by decide +kernel)

theorem test256_block_1 : Interval test256 16 32 :=
  interval_of_check test256 16 16 (by decide +kernel)

theorem test256_block_2 : Interval test256 32 48 :=
  interval_of_check test256 32 16 (by decide +kernel)

theorem test256_block_3 : Interval test256 48 64 :=
  interval_of_check test256 48 16 (by decide +kernel)

theorem test256_block_4 : Interval test256 64 80 :=
  interval_of_check test256 64 16 (by decide +kernel)

theorem test256_block_5 : Interval test256 80 96 :=
  interval_of_check test256 80 16 (by decide +kernel)

theorem test256_block_6 : Interval test256 96 112 :=
  interval_of_check test256 96 16 (by decide +kernel)

theorem test256_block_7 : Interval test256 112 127 :=
  interval_of_check test256 112 15 (by decide +kernel)

theorem test256_complete : Interval test256 0 127 :=
  (interval_append test256 0 64 127
  (interval_append test256 0 32 64
  (interval_append test256 0 16 32
  test256_block_0
  test256_block_1)
  (interval_append test256 32 48 64
  test256_block_2
  test256_block_3))
  (interval_append test256 64 96 127
  (interval_append test256 64 80 96
  test256_block_4
  test256_block_5)
  (interval_append test256 96 112 127
  test256_block_6
  test256_block_7)))
theorem routeInterval256 : Interval routeTest 256 383 := by
  intro i hlo hhi
  have h := test256_complete (i - 256) (Nat.zero_le _) (by omega)
  simpa only [test256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0333

/- Original module: RootedQuotaTransfer0333. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0333
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 383 :=
  (interval_append routeTest 0 128 383
  routeInterval0
  (interval_append routeTest 128 256 383
  routeInterval128
  routeInterval256))

theorem disposition_checked (j : Fin 383) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0333.quota
      ((RootedForests.RootedSubsumedForest0338.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0333.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0333.rawLeaves 11 RootedForests.RootedSubsumedForest0333.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0333.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0338.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0333

/- Original module: RootedQuotaTransfer0335Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0335
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 335: use the complete forest for case 339, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0335.quota k ≤ RootedForests.RootedSubsumedForest0339.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0335.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0335.rawLeaves 1 (RootedForests.RootedSubsumedForest0339.rawLeaves i) (routes.get i)

def disposition (j : Fin 29) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0335.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0335

/- Original module: RootedQuotaTransfer0335Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0335
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 29 :=
  interval_of_check test0 16 13 (by decide +kernel)

theorem test0_complete : Interval test0 0 29 :=
  (interval_append test0 0 16 29
  test0_block_0
  test0_block_1)
theorem routeInterval0 : Interval routeTest 0 29 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0335

/- Original module: RootedQuotaTransfer0335. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0335
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 29 :=
  routeInterval0

theorem disposition_checked (j : Fin 29) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0335.quota
      ((RootedForests.RootedSubsumedForest0339.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0335.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0335.rawLeaves 1 RootedForests.RootedSubsumedForest0335.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0335.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0339.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0335
