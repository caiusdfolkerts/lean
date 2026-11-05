module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0755Dispositions
public import RootedSubsumedForest0803Data
public import RootedSubsumedForest0769Dispositions
public import RootedSubsumedForest0816Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0755Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0755
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 755: use the complete forest for case 803, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0755.quota k ≤ RootedForests.RootedSubsumedForest0803.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0755.quota RootedCaches.RootedSixExtra04.rawCells
    RootedForests.RootedSubsumedForest0755.rawLeaves 1 (RootedForests.RootedSubsumedForest0803.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0755.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0755

/- Original module: RootedQuotaTransfer0755Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0755
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0755

/- Original module: RootedQuotaTransfer0755. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0755
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0755.quota
      ((RootedForests.RootedSubsumedForest0803.rawLeaves j.val).map RootedCaches.RootedSixExtra04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0755.quota RootedCaches.RootedSixExtra04.rawCells
    RootedForests.RootedSubsumedForest0755.rawLeaves 1 RootedForests.RootedSubsumedForest0755.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0755.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0803.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0755

/- Original module: RootedQuotaTransfer0769Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0769
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 769: use the complete forest for case 816, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0769.quota k ≤ RootedForests.RootedSubsumedForest0816.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0769.quota RootedCaches.RootedSixExtra04.rawCells
    RootedForests.RootedSubsumedForest0769.rawLeaves 1 (RootedForests.RootedSubsumedForest0816.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0769.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0769

/- Original module: RootedQuotaTransfer0769Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0769
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0769

/- Original module: RootedQuotaTransfer0769. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0769
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0769.quota
      ((RootedForests.RootedSubsumedForest0816.rawLeaves j.val).map RootedCaches.RootedSixExtra04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0769.quota RootedCaches.RootedSixExtra04.rawCells
    RootedForests.RootedSubsumedForest0769.rawLeaves 1 RootedForests.RootedSubsumedForest0769.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0769.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0816.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0769
