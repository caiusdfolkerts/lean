module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0751Dispositions
public import RootedSubsumedForest0799Data
public import RootedSubsumedForest0765Dispositions
public import RootedSubsumedForest0812Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0751Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0751
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 751: use the complete forest for case 799, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0751.quota k ≤ RootedForests.RootedSubsumedForest0799.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0751.quota RootedCaches.RootedSixExtra00.rawCells
    RootedForests.RootedSubsumedForest0751.rawLeaves 1 (RootedForests.RootedSubsumedForest0799.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0751.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0751

/- Original module: RootedQuotaTransfer0751Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0751
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0751

/- Original module: RootedQuotaTransfer0751. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0751
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0751.quota
      ((RootedForests.RootedSubsumedForest0799.rawLeaves j.val).map RootedCaches.RootedSixExtra00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0751.quota RootedCaches.RootedSixExtra00.rawCells
    RootedForests.RootedSubsumedForest0751.rawLeaves 1 RootedForests.RootedSubsumedForest0751.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0751.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0799.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0751

/- Original module: RootedQuotaTransfer0765Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0765
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 765: use the complete forest for case 812, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0765.quota k ≤ RootedForests.RootedSubsumedForest0812.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0765.quota RootedCaches.RootedSixExtra00.rawCells
    RootedForests.RootedSubsumedForest0765.rawLeaves 1 (RootedForests.RootedSubsumedForest0812.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0765.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0765

/- Original module: RootedQuotaTransfer0765Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0765
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0765

/- Original module: RootedQuotaTransfer0765. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0765
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0765.quota
      ((RootedForests.RootedSubsumedForest0812.rawLeaves j.val).map RootedCaches.RootedSixExtra00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0765.quota RootedCaches.RootedSixExtra00.rawCells
    RootedForests.RootedSubsumedForest0765.rawLeaves 1 RootedForests.RootedSubsumedForest0765.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0765.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0812.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0765
