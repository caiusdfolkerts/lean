module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0643Dispositions
public import RootedSubsumedForest0670Data
public import RootedSubsumedForest0646Dispositions
public import RootedSubsumedForest0697Data
public import RootedSubsumedForest0648Dispositions
public import RootedSubsumedForest0699Data
public import RootedSubsumedForest0650Dispositions
public import RootedSubsumedForest0682Data
public import RootedSubsumedForest0659Dispositions
public import RootedSubsumedForest0687Data
public import RootedSubsumedForest0661Dispositions
public import RootedSubsumedForest0689Data
public import RootedSubsumedForest0663Dispositions
public import RootedSubsumedForest0705Data
public import RootedSubsumedForest0673Dispositions
public import RootedSubsumedForest0675Dispositions
public import RootedSubsumedForest0677Dispositions
public import RootedSubsumedForest0707Data
public import RootedSubsumedForest0684Dispositions
public import RootedSubsumedForest0703Data
public import RootedSubsumedForest0691Dispositions
public import RootedSubsumedForest0701Dispositions
public import RootedSubsumedForest0725Dispositions
public import RootedSubsumedForest0734Data
public import RootedSubsumedForest0726Dispositions
public import RootedSubsumedForest0731Data
public import RootedSubsumedForest0727Dispositions
public import RootedSubsumedForest0737Data
public import RootedSubsumedForest0728Dispositions
public import RootedSubsumedForest0729Dispositions
public import RootedSubsumedForest0740Data
public import RootedSubsumedForest0730Dispositions
public import RootedSubsumedForest0732Dispositions
public import RootedSubsumedForest0733Dispositions
public import RootedSubsumedForest0742Data
public import RootedSubsumedForest0735Dispositions
public import RootedSubsumedForest0736Dispositions
public import RootedSubsumedForest0743Data
public import RootedSubsumedForest0738Dispositions
public import RootedSubsumedForest0741Dispositions

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0643Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0643
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 643: use the complete forest for case 670, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0643.quota k ≤ RootedForests.RootedSubsumedForest0670.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0643.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0643.rawLeaves 1 (RootedForests.RootedSubsumedForest0670.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0643.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0643

/- Original module: RootedQuotaTransfer0643Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0643
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0643

/- Original module: RootedQuotaTransfer0643. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0643
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0643.quota
      ((RootedForests.RootedSubsumedForest0670.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0643.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0643.rawLeaves 1 RootedForests.RootedSubsumedForest0643.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0643.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0670.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0643

/- Original module: RootedQuotaTransfer0646Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0646
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 646: use the complete forest for case 697, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0646.quota k ≤ RootedForests.RootedSubsumedForest0697.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0646.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0646.rawLeaves 1 (RootedForests.RootedSubsumedForest0697.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0646.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0646

/- Original module: RootedQuotaTransfer0646Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0646
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0646

/- Original module: RootedQuotaTransfer0646. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0646
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0646.quota
      ((RootedForests.RootedSubsumedForest0697.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0646.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0646.rawLeaves 1 RootedForests.RootedSubsumedForest0646.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0646.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0697.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0646

/- Original module: RootedQuotaTransfer0648Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0648
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 648: use the complete forest for case 699, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0648.quota k ≤ RootedForests.RootedSubsumedForest0699.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0648.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0648.rawLeaves 1 (RootedForests.RootedSubsumedForest0699.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0648.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0648

/- Original module: RootedQuotaTransfer0648Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0648
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0648

/- Original module: RootedQuotaTransfer0648. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0648
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0648.quota
      ((RootedForests.RootedSubsumedForest0699.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0648.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0648.rawLeaves 1 RootedForests.RootedSubsumedForest0648.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0648.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0699.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0648

/- Original module: RootedQuotaTransfer0650Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0650
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 650: use the complete forest for case 682, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0650.quota k ≤ RootedForests.RootedSubsumedForest0682.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0650.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0650.rawLeaves 1 (RootedForests.RootedSubsumedForest0682.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0650.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0650

/- Original module: RootedQuotaTransfer0650Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0650
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0650

/- Original module: RootedQuotaTransfer0650. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0650
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0650.quota
      ((RootedForests.RootedSubsumedForest0682.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0650.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0650.rawLeaves 1 RootedForests.RootedSubsumedForest0650.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0650.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0682.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0650

/- Original module: RootedQuotaTransfer0659Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0659
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 659: use the complete forest for case 687, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0659.quota k ≤ RootedForests.RootedSubsumedForest0687.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0659.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0659.rawLeaves 1 (RootedForests.RootedSubsumedForest0687.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0659.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0659

/- Original module: RootedQuotaTransfer0659Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0659
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0659

/- Original module: RootedQuotaTransfer0659. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0659
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0659.quota
      ((RootedForests.RootedSubsumedForest0687.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0659.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0659.rawLeaves 1 RootedForests.RootedSubsumedForest0659.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0659.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0687.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0659

/- Original module: RootedQuotaTransfer0661Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0661
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 661: use the complete forest for case 689, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0661.quota k ≤ RootedForests.RootedSubsumedForest0689.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0661.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0661.rawLeaves 1 (RootedForests.RootedSubsumedForest0689.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0661.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0661

/- Original module: RootedQuotaTransfer0661Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0661
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0661

/- Original module: RootedQuotaTransfer0661. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0661
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0661.quota
      ((RootedForests.RootedSubsumedForest0689.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0661.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0661.rawLeaves 1 RootedForests.RootedSubsumedForest0661.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0661.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0689.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0661

/- Original module: RootedQuotaTransfer0663Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0663
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 663: use the complete forest for case 705, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0663.quota k ≤ RootedForests.RootedSubsumedForest0705.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0663.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0663.rawLeaves 1 (RootedForests.RootedSubsumedForest0705.rawLeaves i) (routes.get i)

def disposition (j : Fin 3) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0663.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0663

/- Original module: RootedQuotaTransfer0663Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0663
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 3 :=
  interval_of_check test0 0 3 (by decide +kernel)

theorem test0_complete : Interval test0 0 3 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 3 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0663

/- Original module: RootedQuotaTransfer0663. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0663
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 3 :=
  routeInterval0

theorem disposition_checked (j : Fin 3) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0663.quota
      ((RootedForests.RootedSubsumedForest0705.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0663.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0663.rawLeaves 1 RootedForests.RootedSubsumedForest0663.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0663.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0705.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0663

/- Original module: RootedQuotaTransfer0673Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0673
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 673: use the complete forest for case 697, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0673.quota k ≤ RootedForests.RootedSubsumedForest0697.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0673.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0673.rawLeaves 1 (RootedForests.RootedSubsumedForest0697.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0673.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0673

/- Original module: RootedQuotaTransfer0673Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0673
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0673

/- Original module: RootedQuotaTransfer0673. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0673
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0673.quota
      ((RootedForests.RootedSubsumedForest0697.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0673.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0673.rawLeaves 1 RootedForests.RootedSubsumedForest0673.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0673.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0697.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0673

/- Original module: RootedQuotaTransfer0675Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0675
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 675: use the complete forest for case 699, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0675.quota k ≤ RootedForests.RootedSubsumedForest0699.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0675.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0675.rawLeaves 1 (RootedForests.RootedSubsumedForest0699.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0675.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0675

/- Original module: RootedQuotaTransfer0675Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0675
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0675

/- Original module: RootedQuotaTransfer0675. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0675
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0675.quota
      ((RootedForests.RootedSubsumedForest0699.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0675.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0675.rawLeaves 1 RootedForests.RootedSubsumedForest0675.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0675.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0699.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0675

/- Original module: RootedQuotaTransfer0677Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0677
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 677: use the complete forest for case 707, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0677.quota k ≤ RootedForests.RootedSubsumedForest0707.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0677.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0677.rawLeaves 1 (RootedForests.RootedSubsumedForest0707.rawLeaves i) (routes.get i)

def disposition (j : Fin 18) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0677.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0677

/- Original module: RootedQuotaTransfer0677Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0677
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 18 :=
  interval_of_check test0 16 2 (by decide +kernel)

theorem test0_complete : Interval test0 0 18 :=
  (interval_append test0 0 16 18
  test0_block_0
  test0_block_1)
theorem routeInterval0 : Interval routeTest 0 18 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0677

/- Original module: RootedQuotaTransfer0677. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0677
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 18 :=
  routeInterval0

theorem disposition_checked (j : Fin 18) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0677.quota
      ((RootedForests.RootedSubsumedForest0707.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0677.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0677.rawLeaves 1 RootedForests.RootedSubsumedForest0677.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0677.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0707.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0677

/- Original module: RootedQuotaTransfer0684Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0684
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 684: use the complete forest for case 703, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0684.quota k ≤ RootedForests.RootedSubsumedForest0703.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0684.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0684.rawLeaves 1 (RootedForests.RootedSubsumedForest0703.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0684.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0684

/- Original module: RootedQuotaTransfer0684Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0684
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0684

/- Original module: RootedQuotaTransfer0684. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0684
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0684.quota
      ((RootedForests.RootedSubsumedForest0703.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0684.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0684.rawLeaves 1 RootedForests.RootedSubsumedForest0684.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0684.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0703.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0684

/- Original module: RootedQuotaTransfer0691Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0691
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 691: use the complete forest for case 705, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0691.quota k ≤ RootedForests.RootedSubsumedForest0705.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0691.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0691.rawLeaves 1 (RootedForests.RootedSubsumedForest0705.rawLeaves i) (routes.get i)

def disposition (j : Fin 3) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0691.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0691

/- Original module: RootedQuotaTransfer0691Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0691
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 3 :=
  interval_of_check test0 0 3 (by decide +kernel)

theorem test0_complete : Interval test0 0 3 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 3 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0691

/- Original module: RootedQuotaTransfer0691. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0691
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 3 :=
  routeInterval0

theorem disposition_checked (j : Fin 3) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0691.quota
      ((RootedForests.RootedSubsumedForest0705.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0691.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0691.rawLeaves 1 RootedForests.RootedSubsumedForest0691.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0691.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0705.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0691

/- Original module: RootedQuotaTransfer0701Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0701
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 701: use the complete forest for case 707, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0701.quota k ≤ RootedForests.RootedSubsumedForest0707.quota k := by
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
(.branch 9
 (.leaf (.quota 1))
 (.branch 13
 (.leaf (.quota 1))
 (.branch 15
 (.leaf (.quota 1))
 (.branch 16
 (.leaf (.quota 1))
 (.branch 17
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0701.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0701.rawLeaves 1 (RootedForests.RootedSubsumedForest0707.rawLeaves i) (routes.get i)

def disposition (j : Fin 18) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0701.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0701

/- Original module: RootedQuotaTransfer0701Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0701
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 18 :=
  interval_of_check test0 16 2 (by decide +kernel)

theorem test0_complete : Interval test0 0 18 :=
  (interval_append test0 0 16 18
  test0_block_0
  test0_block_1)
theorem routeInterval0 : Interval routeTest 0 18 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0701

/- Original module: RootedQuotaTransfer0701. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0701
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 18 :=
  routeInterval0

theorem disposition_checked (j : Fin 18) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0701.quota
      ((RootedForests.RootedSubsumedForest0707.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0701.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0701.rawLeaves 1 RootedForests.RootedSubsumedForest0701.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0701.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0707.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0701

/- Original module: RootedQuotaTransfer0725Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0725
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 725: use the complete forest for case 734, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0725.quota k ≤ RootedForests.RootedSubsumedForest0734.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0725.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0725.rawLeaves 1 (RootedForests.RootedSubsumedForest0734.rawLeaves i) (routes.get i)

def disposition (j : Fin 3) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0725.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0725

/- Original module: RootedQuotaTransfer0725Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0725
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 3 :=
  interval_of_check test0 0 3 (by decide +kernel)

theorem test0_complete : Interval test0 0 3 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 3 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0725

/- Original module: RootedQuotaTransfer0725. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0725
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 3 :=
  routeInterval0

theorem disposition_checked (j : Fin 3) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0725.quota
      ((RootedForests.RootedSubsumedForest0734.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0725.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0725.rawLeaves 1 RootedForests.RootedSubsumedForest0725.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0725.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0734.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0725

/- Original module: RootedQuotaTransfer0726Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0726
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 726: use the complete forest for case 731, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0726.quota k ≤ RootedForests.RootedSubsumedForest0731.quota k := by
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
(.leaf (.quota 2))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0726.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0726.rawLeaves 1 (RootedForests.RootedSubsumedForest0731.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0726.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0726

/- Original module: RootedQuotaTransfer0726Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0726
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0726

/- Original module: RootedQuotaTransfer0726. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0726
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0726.quota
      ((RootedForests.RootedSubsumedForest0731.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0726.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0726.rawLeaves 1 RootedForests.RootedSubsumedForest0726.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0726.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0731.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0726

/- Original module: RootedQuotaTransfer0727Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0727
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 727: use the complete forest for case 737, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0727.quota k ≤ RootedForests.RootedSubsumedForest0737.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0727.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0727.rawLeaves 1 (RootedForests.RootedSubsumedForest0737.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0727.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0727

/- Original module: RootedQuotaTransfer0727Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0727
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0727

/- Original module: RootedQuotaTransfer0727. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0727
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0727.quota
      ((RootedForests.RootedSubsumedForest0737.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0727.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0727.rawLeaves 1 RootedForests.RootedSubsumedForest0727.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0727.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0737.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0727

/- Original module: RootedQuotaTransfer0728Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0728
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 728: use the complete forest for case 734, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0728.quota k ≤ RootedForests.RootedSubsumedForest0734.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0728.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0728.rawLeaves 1 (RootedForests.RootedSubsumedForest0734.rawLeaves i) (routes.get i)

def disposition (j : Fin 3) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0728.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0728

/- Original module: RootedQuotaTransfer0728Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0728
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 3 :=
  interval_of_check test0 0 3 (by decide +kernel)

theorem test0_complete : Interval test0 0 3 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 3 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0728

/- Original module: RootedQuotaTransfer0728. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0728
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 3 :=
  routeInterval0

theorem disposition_checked (j : Fin 3) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0728.quota
      ((RootedForests.RootedSubsumedForest0734.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0728.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0728.rawLeaves 1 RootedForests.RootedSubsumedForest0728.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0728.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0734.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0728

/- Original module: RootedQuotaTransfer0729Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0729
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 729: use the complete forest for case 740, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0729.quota k ≤ RootedForests.RootedSubsumedForest0740.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0729.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0729.rawLeaves 1 (RootedForests.RootedSubsumedForest0740.rawLeaves i) (routes.get i)

def disposition (j : Fin 25) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0729.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0729

/- Original module: RootedQuotaTransfer0729Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0729
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 25 :=
  interval_of_check test0 16 9 (by decide +kernel)

theorem test0_complete : Interval test0 0 25 :=
  (interval_append test0 0 16 25
  test0_block_0
  test0_block_1)
theorem routeInterval0 : Interval routeTest 0 25 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0729

/- Original module: RootedQuotaTransfer0729. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0729
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 25 :=
  routeInterval0

theorem disposition_checked (j : Fin 25) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0729.quota
      ((RootedForests.RootedSubsumedForest0740.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0729.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0729.rawLeaves 1 RootedForests.RootedSubsumedForest0729.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0729.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0740.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0729

/- Original module: RootedQuotaTransfer0730Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0730
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 730: use the complete forest for case 737, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0730.quota k ≤ RootedForests.RootedSubsumedForest0737.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0730.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0730.rawLeaves 1 (RootedForests.RootedSubsumedForest0737.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0730.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0730

/- Original module: RootedQuotaTransfer0730Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0730
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0730

/- Original module: RootedQuotaTransfer0730. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0730
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0730.quota
      ((RootedForests.RootedSubsumedForest0737.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0730.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0730.rawLeaves 1 RootedForests.RootedSubsumedForest0730.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0730.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0737.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0730

/- Original module: RootedQuotaTransfer0732Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0732
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 732: use the complete forest for case 737, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0732.quota k ≤ RootedForests.RootedSubsumedForest0737.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0732.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0732.rawLeaves 1 (RootedForests.RootedSubsumedForest0737.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0732.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0732

/- Original module: RootedQuotaTransfer0732Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0732
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0732

/- Original module: RootedQuotaTransfer0732. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0732
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0732.quota
      ((RootedForests.RootedSubsumedForest0737.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0732.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0732.rawLeaves 1 RootedForests.RootedSubsumedForest0732.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0732.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0737.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0732

/- Original module: RootedQuotaTransfer0733Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0733
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 733: use the complete forest for case 742, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0733.quota k ≤ RootedForests.RootedSubsumedForest0742.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0733.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0733.rawLeaves 1 (RootedForests.RootedSubsumedForest0742.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0733.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0733

/- Original module: RootedQuotaTransfer0733Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0733
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 4 :=
  interval_of_check test0 0 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 4 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 4 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0733

/- Original module: RootedQuotaTransfer0733. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0733
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0733.quota
      ((RootedForests.RootedSubsumedForest0742.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0733.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0733.rawLeaves 1 RootedForests.RootedSubsumedForest0733.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0733.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0742.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0733

/- Original module: RootedQuotaTransfer0735Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0735
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 735: use the complete forest for case 740, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0735.quota k ≤ RootedForests.RootedSubsumedForest0740.quota k := by
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
(.branch 12
 (.leaf (.quota 1))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.quota 2))
 (.branch 14
 (.leaf (.quota 1))
 (.leaf (.reuse 1))))
 (.branch 16
 (.leaf (.quota 1))
 (.branch 17
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 21
 (.branch 19
 (.leaf (.reuse 3))
 (.leaf (.quota 1)))
 (.branch 23
 (.leaf (.quota 1))
 (.branch 24
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0735.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0735.rawLeaves 5 (RootedForests.RootedSubsumedForest0740.rawLeaves i) (routes.get i)

def disposition (j : Fin 25) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0735.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0735

/- Original module: RootedQuotaTransfer0735Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0735
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 25 :=
  interval_of_check test0 16 9 (by decide +kernel)

theorem test0_complete : Interval test0 0 25 :=
  (interval_append test0 0 16 25
  test0_block_0
  test0_block_1)
theorem routeInterval0 : Interval routeTest 0 25 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0735

/- Original module: RootedQuotaTransfer0735. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0735
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 25 :=
  routeInterval0

theorem disposition_checked (j : Fin 25) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0735.quota
      ((RootedForests.RootedSubsumedForest0740.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0735.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0735.rawLeaves 5 RootedForests.RootedSubsumedForest0735.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0735.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0740.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0735

/- Original module: RootedQuotaTransfer0736Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0736
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 736: use the complete forest for case 743, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0736.quota k ≤ RootedForests.RootedSubsumedForest0743.quota k := by
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
(.branch 225
 (.branch 112
 (.branch 56
 (.leaf (.quota 1))
 (.branch 84
 (.leaf (.quota 1))
 (.branch 98
 (.branch 91
 (.leaf (.quota 1))
 (.branch 94
 (.leaf (.quota 1))
 (.branch 96
 (.leaf (.quota 1))
 (.branch 97
 (.leaf (.reuse 0))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 338
 (.branch 281
 (.leaf (.quota 1))
 (.branch 309
 (.leaf (.quota 1))
 (.branch 323
 (.leaf (.quota 1))
 (.branch 330
 (.leaf (.quota 1))
 (.branch 334
 (.leaf (.quota 1))
 (.branch 336
 (.leaf (.quota 1))
 (.branch 337
 (.leaf (.quota 1))
 (.leaf (.reuse 1)))))))))
 (.branch 394
 (.leaf (.quota 1))
 (.branch 422
 (.branch 408
 (.branch 401
 (.branch 397
 (.branch 395
 (.leaf (.reuse 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 436
 (.leaf (.quota 1))
 (.branch 443
 (.branch 439
 (.branch 437
 (.leaf (.quota 1))
 (.branch 438
 (.leaf (.quota 1))
 (.leaf (.reuse 3))))
 (.leaf (.quota 1)))
 (.branch 447
 (.leaf (.quota 1))
 (.branch 449
 (.branch 448
 (.leaf (.quota 1))
 (.leaf (.reuse 4)))
 (.leaf (.quota 1))))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0736.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0736.rawLeaves 5 (RootedForests.RootedSubsumedForest0743.rawLeaves i) (routes.get i)

def disposition (j : Fin 451) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0736.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0736

/- Original module: RootedQuotaTransfer0736Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0736
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0736

/- Original module: RootedQuotaTransfer0736Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0736
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0736

/- Original module: RootedQuotaTransfer0736Proof002. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0736
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

theorem test256_block_7 : Interval test256 112 128 :=
  interval_of_check test256 112 16 (by decide +kernel)

theorem test256_complete : Interval test256 0 128 :=
  (interval_append test256 0 64 128
  (interval_append test256 0 32 64
  (interval_append test256 0 16 32
  test256_block_0
  test256_block_1)
  (interval_append test256 32 48 64
  test256_block_2
  test256_block_3))
  (interval_append test256 64 96 128
  (interval_append test256 64 80 96
  test256_block_4
  test256_block_5)
  (interval_append test256 96 112 128
  test256_block_6
  test256_block_7)))
theorem routeInterval256 : Interval routeTest 256 384 := by
  intro i hlo hhi
  have h := test256_complete (i - 256) (Nat.zero_le _) (by omega)
  simpa only [test256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0736

/- Original module: RootedQuotaTransfer0736Proof003. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0736
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test384 (i : Nat) := routeTest (i + 384)
theorem test384_block_0 : Interval test384 0 16 :=
  interval_of_check test384 0 16 (by decide +kernel)

theorem test384_block_1 : Interval test384 16 32 :=
  interval_of_check test384 16 16 (by decide +kernel)

theorem test384_block_2 : Interval test384 32 48 :=
  interval_of_check test384 32 16 (by decide +kernel)

theorem test384_block_3 : Interval test384 48 64 :=
  interval_of_check test384 48 16 (by decide +kernel)

theorem test384_block_4 : Interval test384 64 67 :=
  interval_of_check test384 64 3 (by decide +kernel)

theorem test384_complete : Interval test384 0 67 :=
  (interval_append test384 0 32 67
  (interval_append test384 0 16 32
  test384_block_0
  test384_block_1)
  (interval_append test384 32 48 67
  test384_block_2
  (interval_append test384 48 64 67
  test384_block_3
  test384_block_4)))
theorem routeInterval384 : Interval routeTest 384 451 := by
  intro i hlo hhi
  have h := test384_complete (i - 384) (Nat.zero_le _) (by omega)
  simpa only [test384, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0736

/- Original module: RootedQuotaTransfer0736. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0736
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 451 :=
  (interval_append routeTest 0 256 451
  (interval_append routeTest 0 128 256
  routeInterval0
  routeInterval128)
  (interval_append routeTest 256 384 451
  routeInterval256
  routeInterval384))

theorem disposition_checked (j : Fin 451) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0736.quota
      ((RootedForests.RootedSubsumedForest0743.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0736.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0736.rawLeaves 5 RootedForests.RootedSubsumedForest0736.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0736.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0743.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0736

/- Original module: RootedQuotaTransfer0738Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0738
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 738: use the complete forest for case 742, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0738.quota k ≤ RootedForests.RootedSubsumedForest0742.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0738.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0738.rawLeaves 1 (RootedForests.RootedSubsumedForest0742.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0738.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0738

/- Original module: RootedQuotaTransfer0738Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0738
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 4 :=
  interval_of_check test0 0 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 4 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 4 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0738

/- Original module: RootedQuotaTransfer0738. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0738
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0738.quota
      ((RootedForests.RootedSubsumedForest0742.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0738.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0738.rawLeaves 1 RootedForests.RootedSubsumedForest0738.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0738.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0742.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0738

/- Original module: RootedQuotaTransfer0741Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0741
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 741: use the complete forest for case 743, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0741.quota k ≤ RootedForests.RootedSubsumedForest0743.quota k := by
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
(.branch 225
 (.branch 112
 (.branch 56
 (.branch 28
 (.leaf (.quota 1))
 (.branch 42
 (.branch 35
 (.branch 31
 (.leaf (.quota 1))
 (.branch 33
 (.leaf (.quota 1))
 (.branch 34
 (.leaf (.reuse 0))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 49
 (.branch 45
 (.leaf (.quota 1))
 (.branch 47
 (.branch 46
 (.leaf (.quota 1))
 (.leaf (.reuse 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 84
 (.branch 70
 (.branch 63
 (.branch 59
 (.leaf (.quota 1))
 (.branch 61
 (.branch 60
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 77
 (.leaf (.quota 1))
 (.branch 80
 (.branch 78
 (.leaf (.quota 1))
 (.branch 79
 (.leaf (.quota 1))
 (.leaf (.reuse 3))))
 (.leaf (.quota 1)))))
 (.branch 98
 (.branch 91
 (.branch 87
 (.branch 85
 (.leaf (.quota 1))
 (.branch 86
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 89
 (.leaf (.quota 1))
 (.branch 90
 (.leaf (.reuse 5))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 168
 (.branch 140
 (.branch 126
 (.branch 119
 (.leaf (.quota 1))
 (.branch 122
 (.branch 120
 (.leaf (.quota 1))
 (.branch 121
 (.leaf (.reuse 7))
 (.leaf (.reuse 8))))
 (.branch 124
 (.branch 123
 (.leaf (.reuse 9))
 (.leaf (.reuse 10)))
 (.leaf (.quota 1)))))
 (.branch 133
 (.branch 129
 (.branch 127
 (.leaf (.quota 2))
 (.branch 128
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 136
 (.branch 134
 (.leaf (.quota 1))
 (.branch 135
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 138
 (.leaf (.quota 2))
 (.branch 139
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.leaf (.quota 1)))
 (.branch 196
 (.branch 182
 (.leaf (.quota 1))
 (.branch 189
 (.branch 185
 (.branch 183
 (.leaf (.quota 1))
 (.branch 184
 (.leaf (.reuse 17))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 338
 (.branch 281
 (.branch 253
 (.branch 239
 (.branch 232
 (.branch 228
 (.branch 226
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 235
 (.branch 233
 (.leaf (.quota 1))
 (.branch 234
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 237
 (.branch 236
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 246
 (.leaf (.quota 1))
 (.branch 249
 (.branch 247
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 267
 (.leaf (.quota 1))
 (.branch 274
 (.branch 270
 (.branch 268
 (.leaf (.quota 1))
 (.branch 269
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 309
 (.branch 295
 (.leaf (.quota 1))
 (.branch 302
 (.branch 298
 (.branch 296
 (.leaf (.quota 1))
 (.branch 297
 (.leaf (.quota 1))
 (.leaf (.reuse 23))))
 (.leaf (.quota 1)))
 (.branch 305
 (.branch 303
 (.leaf (.quota 1))
 (.branch 304
 (.leaf (.reuse 24))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 323
 (.branch 316
 (.branch 312
 (.leaf (.quota 1))
 (.branch 314
 (.leaf (.quota 1))
 (.branch 315
 (.leaf (.reuse 25))
 (.leaf (.quota 1)))))
 (.branch 319
 (.leaf (.quota 1))
 (.branch 321
 (.branch 320
 (.leaf (.reuse 26))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 330
 (.branch 326
 (.branch 324
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 328
 (.leaf (.quota 1))
 (.branch 329
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.branch 334
 (.branch 332
 (.branch 331
 (.leaf (.reuse 29))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 394
 (.branch 366
 (.branch 352
 (.branch 345
 (.branch 341
 (.branch 339
 (.leaf (.quota 1))
 (.branch 340
 (.leaf (.reuse 31))
 (.leaf (.reuse 32))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 359
 (.branch 355
 (.leaf (.quota 1))
 (.branch 357
 (.branch 356
 (.leaf (.quota 1))
 (.leaf (.reuse 33)))
 (.branch 358
 (.leaf (.reuse 34))
 (.leaf (.quota 1)))))
 (.branch 362
 (.branch 360
 (.leaf (.reuse 35))
 (.branch 361
 (.leaf (.reuse 36))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 380
 (.branch 373
 (.branch 369
 (.branch 367
 (.leaf (.quota 1))
 (.branch 368
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 422
 (.branch 408
 (.branch 401
 (.leaf (.quota 1))
 (.branch 404
 (.leaf (.quota 1))
 (.branch 406
 (.branch 405
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 407
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))
 (.branch 436
 (.leaf (.quota 1))
 (.branch 443
 (.branch 439
 (.leaf (.quota 1))
 (.branch 441
 (.branch 440
 (.leaf (.quota 1))
 (.leaf (.reuse 42)))
 (.branch 442
 (.leaf (.reuse 43))
 (.leaf (.quota 1)))))
 (.branch 447
 (.branch 445
 (.branch 444
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 449
 (.leaf (.quota 1))
 (.branch 450
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0741.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0741.rawLeaves 47 (RootedForests.RootedSubsumedForest0743.rawLeaves i) (routes.get i)

def disposition (j : Fin 451) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0741.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0741

/- Original module: RootedQuotaTransfer0741Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0741
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0741

/- Original module: RootedQuotaTransfer0741Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0741
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0741

/- Original module: RootedQuotaTransfer0741Proof002. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0741
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

theorem test256_block_7 : Interval test256 112 128 :=
  interval_of_check test256 112 16 (by decide +kernel)

theorem test256_complete : Interval test256 0 128 :=
  (interval_append test256 0 64 128
  (interval_append test256 0 32 64
  (interval_append test256 0 16 32
  test256_block_0
  test256_block_1)
  (interval_append test256 32 48 64
  test256_block_2
  test256_block_3))
  (interval_append test256 64 96 128
  (interval_append test256 64 80 96
  test256_block_4
  test256_block_5)
  (interval_append test256 96 112 128
  test256_block_6
  test256_block_7)))
theorem routeInterval256 : Interval routeTest 256 384 := by
  intro i hlo hhi
  have h := test256_complete (i - 256) (Nat.zero_le _) (by omega)
  simpa only [test256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0741

/- Original module: RootedQuotaTransfer0741Proof003. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0741
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test384 (i : Nat) := routeTest (i + 384)
theorem test384_block_0 : Interval test384 0 16 :=
  interval_of_check test384 0 16 (by decide +kernel)

theorem test384_block_1 : Interval test384 16 32 :=
  interval_of_check test384 16 16 (by decide +kernel)

theorem test384_block_2 : Interval test384 32 48 :=
  interval_of_check test384 32 16 (by decide +kernel)

theorem test384_block_3 : Interval test384 48 64 :=
  interval_of_check test384 48 16 (by decide +kernel)

theorem test384_block_4 : Interval test384 64 67 :=
  interval_of_check test384 64 3 (by decide +kernel)

theorem test384_complete : Interval test384 0 67 :=
  (interval_append test384 0 32 67
  (interval_append test384 0 16 32
  test384_block_0
  test384_block_1)
  (interval_append test384 32 48 67
  test384_block_2
  (interval_append test384 48 64 67
  test384_block_3
  test384_block_4)))
theorem routeInterval384 : Interval routeTest 384 451 := by
  intro i hlo hhi
  have h := test384_complete (i - 384) (Nat.zero_le _) (by omega)
  simpa only [test384, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0741

/- Original module: RootedQuotaTransfer0741. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0741
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 451 :=
  (interval_append routeTest 0 256 451
  (interval_append routeTest 0 128 256
  routeInterval0
  routeInterval128)
  (interval_append routeTest 256 384 451
  routeInterval256
  routeInterval384))

theorem disposition_checked (j : Fin 451) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0741.quota
      ((RootedForests.RootedSubsumedForest0743.rawLeaves j.val).map RootedCaches.RootedSixBase04.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0741.quota RootedCaches.RootedSixBase04.rawCells
    RootedForests.RootedSubsumedForest0741.rawLeaves 47 RootedForests.RootedSubsumedForest0741.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0741.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0743.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0741
