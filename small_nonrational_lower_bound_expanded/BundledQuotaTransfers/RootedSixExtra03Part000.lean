module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0754Dispositions
public import RootedSubsumedForest0802Data
public import RootedSubsumedForest0768Dispositions
public import RootedSubsumedForest0815Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0754Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0754
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 754: use the complete forest for case 802, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0754.quota k ≤ RootedForests.RootedSubsumedForest0802.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0754.quota RootedCaches.RootedSixExtra03.rawCells
    RootedForests.RootedSubsumedForest0754.rawLeaves 1 (RootedForests.RootedSubsumedForest0802.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0754.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0754

/- Original module: RootedQuotaTransfer0754Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0754
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0754

/- Original module: RootedQuotaTransfer0754. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0754
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0754.quota
      ((RootedForests.RootedSubsumedForest0802.rawLeaves j.val).map RootedCaches.RootedSixExtra03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0754.quota RootedCaches.RootedSixExtra03.rawCells
    RootedForests.RootedSubsumedForest0754.rawLeaves 1 RootedForests.RootedSubsumedForest0754.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0754.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0802.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0754

/- Original module: RootedQuotaTransfer0768Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0768
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 768: use the complete forest for case 815, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0768.quota k ≤ RootedForests.RootedSubsumedForest0815.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0768.quota RootedCaches.RootedSixExtra03.rawCells
    RootedForests.RootedSubsumedForest0768.rawLeaves 1 (RootedForests.RootedSubsumedForest0815.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0768.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0768

/- Original module: RootedQuotaTransfer0768Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0768
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0768

/- Original module: RootedQuotaTransfer0768. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0768
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0768.quota
      ((RootedForests.RootedSubsumedForest0815.rawLeaves j.val).map RootedCaches.RootedSixExtra03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0768.quota RootedCaches.RootedSixExtra03.rawCells
    RootedForests.RootedSubsumedForest0768.rawLeaves 1 RootedForests.RootedSubsumedForest0768.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0768.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0815.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0768
