module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0744Dispositions
public import RootedSubsumedForest0797Data
public import RootedSubsumedForest0753Dispositions
public import RootedSubsumedForest0801Data
public import RootedSubsumedForest0756Dispositions
public import RootedSubsumedForest0838Data
public import RootedSubsumedForest0767Dispositions
public import RootedSubsumedForest0814Data
public import RootedSubsumedForest0793Dispositions
public import RootedSubsumedForest0855Data
public import RootedSubsumedForest0805Dispositions
public import RootedSubsumedForest0832Dispositions

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0744Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0744
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 744: use the complete forest for case 797, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0744.quota k ≤ RootedForests.RootedSubsumedForest0797.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0744.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0744.rawLeaves 1 (RootedForests.RootedSubsumedForest0797.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0744.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0744

/- Original module: RootedQuotaTransfer0744Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0744
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0744

/- Original module: RootedQuotaTransfer0744. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0744
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0744.quota
      ((RootedForests.RootedSubsumedForest0797.rawLeaves j.val).map RootedCaches.RootedSixExtra02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0744.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0744.rawLeaves 1 RootedForests.RootedSubsumedForest0744.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0744.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0797.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0744

/- Original module: RootedQuotaTransfer0753Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0753
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 753: use the complete forest for case 801, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0753.quota k ≤ RootedForests.RootedSubsumedForest0801.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0753.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0753.rawLeaves 1 (RootedForests.RootedSubsumedForest0801.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0753.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0753

/- Original module: RootedQuotaTransfer0753Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0753
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0753

/- Original module: RootedQuotaTransfer0753. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0753
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0753.quota
      ((RootedForests.RootedSubsumedForest0801.rawLeaves j.val).map RootedCaches.RootedSixExtra02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0753.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0753.rawLeaves 1 RootedForests.RootedSubsumedForest0753.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0753.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0801.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0753

/- Original module: RootedQuotaTransfer0756Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0756
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 756: use the complete forest for case 838, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0756.quota k ≤ RootedForests.RootedSubsumedForest0838.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0756.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0756.rawLeaves 1 (RootedForests.RootedSubsumedForest0838.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0756.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0756

/- Original module: RootedQuotaTransfer0756Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0756
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0756

/- Original module: RootedQuotaTransfer0756. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0756
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0756.quota
      ((RootedForests.RootedSubsumedForest0838.rawLeaves j.val).map RootedCaches.RootedSixExtra02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0756.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0756.rawLeaves 1 RootedForests.RootedSubsumedForest0756.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0756.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0838.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0756

/- Original module: RootedQuotaTransfer0767Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0767
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 767: use the complete forest for case 814, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0767.quota k ≤ RootedForests.RootedSubsumedForest0814.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0767.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0767.rawLeaves 1 (RootedForests.RootedSubsumedForest0814.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0767.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0767

/- Original module: RootedQuotaTransfer0767Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0767
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0767

/- Original module: RootedQuotaTransfer0767. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0767
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0767.quota
      ((RootedForests.RootedSubsumedForest0814.rawLeaves j.val).map RootedCaches.RootedSixExtra02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0767.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0767.rawLeaves 1 RootedForests.RootedSubsumedForest0767.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0767.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0814.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0767

/- Original module: RootedQuotaTransfer0793Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0793
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 793: use the complete forest for case 855, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0793.quota k ≤ RootedForests.RootedSubsumedForest0855.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0793.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0793.rawLeaves 1 (RootedForests.RootedSubsumedForest0855.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0793.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0793

/- Original module: RootedQuotaTransfer0793Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0793
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0793

/- Original module: RootedQuotaTransfer0793. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0793
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0793.quota
      ((RootedForests.RootedSubsumedForest0855.rawLeaves j.val).map RootedCaches.RootedSixExtra02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0793.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0793.rawLeaves 1 RootedForests.RootedSubsumedForest0793.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0793.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0855.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0793

/- Original module: RootedQuotaTransfer0805Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0805
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 805: use the complete forest for case 838, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0805.quota k ≤ RootedForests.RootedSubsumedForest0838.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0805.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0805.rawLeaves 1 (RootedForests.RootedSubsumedForest0838.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0805.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0805

/- Original module: RootedQuotaTransfer0805Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0805
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0805

/- Original module: RootedQuotaTransfer0805. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0805
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0805.quota
      ((RootedForests.RootedSubsumedForest0838.rawLeaves j.val).map RootedCaches.RootedSixExtra02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0805.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0805.rawLeaves 1 RootedForests.RootedSubsumedForest0805.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0805.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0838.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0805

/- Original module: RootedQuotaTransfer0832Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0832
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 832: use the complete forest for case 855, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0832.quota k ≤ RootedForests.RootedSubsumedForest0855.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0832.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0832.rawLeaves 1 (RootedForests.RootedSubsumedForest0855.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0832.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0832

/- Original module: RootedQuotaTransfer0832Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0832
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0832

/- Original module: RootedQuotaTransfer0832. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0832
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0832.quota
      ((RootedForests.RootedSubsumedForest0855.rawLeaves j.val).map RootedCaches.RootedSixExtra02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0832.quota RootedCaches.RootedSixExtra02.rawCells
    RootedForests.RootedSubsumedForest0832.rawLeaves 1 RootedForests.RootedSubsumedForest0832.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0832.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0855.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0832
