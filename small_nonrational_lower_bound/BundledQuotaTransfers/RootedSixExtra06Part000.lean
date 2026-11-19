module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0747Dispositions
public import RootedSubsumedForest0835Data
public import RootedSubsumedForest0750Dispositions
public import RootedSubsumedForest0811Data
public import RootedSubsumedForest0796Dispositions
public import RootedSubsumedForest0798Dispositions
public import RootedSubsumedForest0858Data
public import RootedSubsumedForest0818Dispositions
public import RootedSubsumedForest0844Data
public import RootedSubsumedForest0836Dispositions

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0747Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0747
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 747: use the complete forest for case 835, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0747.quota k ≤ RootedForests.RootedSubsumedForest0835.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0747.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0747.rawLeaves 1 (RootedForests.RootedSubsumedForest0835.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0747.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0747

/- Original module: RootedQuotaTransfer0747Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0747
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0747

/- Original module: RootedQuotaTransfer0747. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0747
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0747.quota
      ((RootedForests.RootedSubsumedForest0835.rawLeaves j.val).map RootedCaches.RootedSixExtra06.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0747.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0747.rawLeaves 1 RootedForests.RootedSubsumedForest0747.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0747.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0835.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0747

/- Original module: RootedQuotaTransfer0750Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0750
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 750: use the complete forest for case 811, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0750.quota k ≤ RootedForests.RootedSubsumedForest0811.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0750.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0750.rawLeaves 1 (RootedForests.RootedSubsumedForest0811.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0750.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0750

/- Original module: RootedQuotaTransfer0750Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0750
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0750

/- Original module: RootedQuotaTransfer0750. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0750
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0750.quota
      ((RootedForests.RootedSubsumedForest0811.rawLeaves j.val).map RootedCaches.RootedSixExtra06.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0750.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0750.rawLeaves 1 RootedForests.RootedSubsumedForest0750.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0750.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0811.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0750

/- Original module: RootedQuotaTransfer0796Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0796
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 796: use the complete forest for case 835, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0796.quota k ≤ RootedForests.RootedSubsumedForest0835.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0796.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0796.rawLeaves 1 (RootedForests.RootedSubsumedForest0835.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0796.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0796

/- Original module: RootedQuotaTransfer0796Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0796
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0796

/- Original module: RootedQuotaTransfer0796. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0796
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0796.quota
      ((RootedForests.RootedSubsumedForest0835.rawLeaves j.val).map RootedCaches.RootedSixExtra06.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0796.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0796.rawLeaves 1 RootedForests.RootedSubsumedForest0796.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0796.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0835.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0796

/- Original module: RootedQuotaTransfer0798Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0798
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 798: use the complete forest for case 858, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0798.quota k ≤ RootedForests.RootedSubsumedForest0858.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0798.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0798.rawLeaves 1 (RootedForests.RootedSubsumedForest0858.rawLeaves i) (routes.get i)

def disposition (j : Fin 50) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0798.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0798

/- Original module: RootedQuotaTransfer0798Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0798
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 50 :=
  interval_of_check test0 48 2 (by decide +kernel)

theorem test0_complete : Interval test0 0 50 :=
  (interval_append test0 0 32 50
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 50
  test0_block_2
  test0_block_3))
theorem routeInterval0 : Interval routeTest 0 50 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0798

/- Original module: RootedQuotaTransfer0798. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0798
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 50 :=
  routeInterval0

theorem disposition_checked (j : Fin 50) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0798.quota
      ((RootedForests.RootedSubsumedForest0858.rawLeaves j.val).map RootedCaches.RootedSixExtra06.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0798.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0798.rawLeaves 1 RootedForests.RootedSubsumedForest0798.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0798.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0858.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0798

/- Original module: RootedQuotaTransfer0818Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0818
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 818: use the complete forest for case 844, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0818.quota k ≤ RootedForests.RootedSubsumedForest0844.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0818.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0818.rawLeaves 1 (RootedForests.RootedSubsumedForest0844.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0818.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0818

/- Original module: RootedQuotaTransfer0818Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0818
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0818

/- Original module: RootedQuotaTransfer0818. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0818
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0818.quota
      ((RootedForests.RootedSubsumedForest0844.rawLeaves j.val).map RootedCaches.RootedSixExtra06.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0818.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0818.rawLeaves 1 RootedForests.RootedSubsumedForest0818.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0818.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0844.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0818

/- Original module: RootedQuotaTransfer0836Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0836
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 836: use the complete forest for case 858, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0836.quota k ≤ RootedForests.RootedSubsumedForest0858.quota k := by
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
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.quota 1))
 (.branch 2
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 16
 (.leaf (.quota 1))
 (.branch 17
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0836.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0836.rawLeaves 3 (RootedForests.RootedSubsumedForest0858.rawLeaves i) (routes.get i)

def disposition (j : Fin 50) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0836.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0836

/- Original module: RootedQuotaTransfer0836Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0836
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 50 :=
  interval_of_check test0 48 2 (by decide +kernel)

theorem test0_complete : Interval test0 0 50 :=
  (interval_append test0 0 32 50
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 50
  test0_block_2
  test0_block_3))
theorem routeInterval0 : Interval routeTest 0 50 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0836

/- Original module: RootedQuotaTransfer0836. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0836
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 50 :=
  routeInterval0

theorem disposition_checked (j : Fin 50) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0836.quota
      ((RootedForests.RootedSubsumedForest0858.rawLeaves j.val).map RootedCaches.RootedSixExtra06.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0836.quota RootedCaches.RootedSixExtra06.rawCells
    RootedForests.RootedSubsumedForest0836.rawLeaves 3 RootedForests.RootedSubsumedForest0836.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0836.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0858.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0836
