module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0129Dispositions
public import RootedSubsumedForest0227Data
public import RootedSubsumedForest0130Dispositions
public import RootedSubsumedForest0228Data
public import RootedSubsumedForest0131Dispositions
public import RootedSubsumedForest0229Data
public import RootedSubsumedForest0132Dispositions
public import RootedSubsumedForest0230Data
public import RootedSubsumedForest0133Dispositions
public import RootedSubsumedForest0231Data
public import RootedSubsumedForest0140Dispositions
public import RootedSubsumedForest0296Data
public import RootedSubsumedForest0141Dispositions
public import RootedSubsumedForest0297Data
public import RootedSubsumedForest0142Dispositions
public import RootedSubsumedForest0298Data
public import RootedSubsumedForest0143Dispositions
public import RootedSubsumedForest0299Data
public import RootedSubsumedForest0144Dispositions
public import RootedSubsumedForest0300Data
public import RootedSubsumedForest0152Dispositions
public import RootedSubsumedForest0308Data
public import RootedSubsumedForest0154Dispositions
public import RootedSubsumedForest0267Data
public import RootedSubsumedForest0197Dispositions
public import RootedSubsumedForest0273Data
public import RootedSubsumedForest0198Dispositions
public import RootedSubsumedForest0274Data
public import RootedSubsumedForest0199Dispositions
public import RootedSubsumedForest0275Data
public import RootedSubsumedForest0200Dispositions
public import RootedSubsumedForest0276Data
public import RootedSubsumedForest0201Dispositions
public import RootedSubsumedForest0277Data
public import RootedSubsumedForest0209Dispositions
public import RootedSubsumedForest0285Data
public import RootedSubsumedForest0212Dispositions
public import RootedSubsumedForest0316Data
public import RootedSubsumedForest0238Dispositions
public import RootedSubsumedForest0239Dispositions
public import RootedSubsumedForest0240Dispositions
public import RootedSubsumedForest0241Dispositions
public import RootedSubsumedForest0242Dispositions
public import RootedSubsumedForest0250Dispositions
public import RootedSubsumedForest0252Dispositions
public import RootedSubsumedForest0319Data
public import RootedSubsumedForest0270Dispositions
public import RootedSubsumedForest0313Data
public import RootedSubsumedForest0288Dispositions
public import RootedSubsumedForest0310Dispositions
public import RootedSubsumedForest0322Dispositions
public import RootedSubsumedForest0331Data
public import RootedSubsumedForest0323Dispositions
public import RootedSubsumedForest0328Data
public import RootedSubsumedForest0324Dispositions
public import RootedSubsumedForest0334Data
public import RootedSubsumedForest0325Dispositions
public import RootedSubsumedForest0326Dispositions
public import RootedSubsumedForest0337Data
public import RootedSubsumedForest0327Dispositions
public import RootedSubsumedForest0329Dispositions
public import RootedSubsumedForest0330Dispositions
public import RootedSubsumedForest0339Data
public import RootedSubsumedForest0332Dispositions
public import RootedSubsumedForest0333Dispositions
public import RootedSubsumedForest0338Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0129Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0129
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 129: use the complete forest for case 227, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0129.quota k ≤ RootedForests.RootedSubsumedForest0227.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0129.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0129.rawLeaves 1 (RootedForests.RootedSubsumedForest0227.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0129.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0129

/- Original module: RootedQuotaTransfer0129Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0129
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0129

/- Original module: RootedQuotaTransfer0129. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0129
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0129.quota
      ((RootedForests.RootedSubsumedForest0227.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0129.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0129.rawLeaves 1 RootedForests.RootedSubsumedForest0129.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0129.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0227.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0129

/- Original module: RootedQuotaTransfer0130Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0130
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 130: use the complete forest for case 228, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0130.quota k ≤ RootedForests.RootedSubsumedForest0228.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0130.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0130.rawLeaves 1 (RootedForests.RootedSubsumedForest0228.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0130.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0130

/- Original module: RootedQuotaTransfer0130Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0130
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0130

/- Original module: RootedQuotaTransfer0130. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0130
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0130.quota
      ((RootedForests.RootedSubsumedForest0228.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0130.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0130.rawLeaves 1 RootedForests.RootedSubsumedForest0130.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0130.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0228.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0130

/- Original module: RootedQuotaTransfer0131Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0131
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 131: use the complete forest for case 229, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0131.quota k ≤ RootedForests.RootedSubsumedForest0229.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0131.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0131.rawLeaves 1 (RootedForests.RootedSubsumedForest0229.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0131.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0131

/- Original module: RootedQuotaTransfer0131Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0131
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0131

/- Original module: RootedQuotaTransfer0131. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0131
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0131.quota
      ((RootedForests.RootedSubsumedForest0229.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0131.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0131.rawLeaves 1 RootedForests.RootedSubsumedForest0131.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0131.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0229.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0131

/- Original module: RootedQuotaTransfer0132Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0132
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 132: use the complete forest for case 230, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0132.quota k ≤ RootedForests.RootedSubsumedForest0230.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0132.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0132.rawLeaves 1 (RootedForests.RootedSubsumedForest0230.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0132.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0132

/- Original module: RootedQuotaTransfer0132Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0132
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0132

/- Original module: RootedQuotaTransfer0132. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0132
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0132.quota
      ((RootedForests.RootedSubsumedForest0230.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0132.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0132.rawLeaves 1 RootedForests.RootedSubsumedForest0132.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0132.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0230.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0132

/- Original module: RootedQuotaTransfer0133Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0133
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 133: use the complete forest for case 231, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0133.quota k ≤ RootedForests.RootedSubsumedForest0231.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0133.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0133.rawLeaves 1 (RootedForests.RootedSubsumedForest0231.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0133.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0133

/- Original module: RootedQuotaTransfer0133Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0133
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0133

/- Original module: RootedQuotaTransfer0133. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0133
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0133.quota
      ((RootedForests.RootedSubsumedForest0231.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0133.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0133.rawLeaves 1 RootedForests.RootedSubsumedForest0133.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0133.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0231.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0133

/- Original module: RootedQuotaTransfer0140Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0140
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 140: use the complete forest for case 296, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0140.quota k ≤ RootedForests.RootedSubsumedForest0296.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0140.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0140.rawLeaves 1 (RootedForests.RootedSubsumedForest0296.rawLeaves i) (routes.get i)

def disposition (j : Fin 7) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0140.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0140

/- Original module: RootedQuotaTransfer0140Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0140
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 7 :=
  interval_of_check test0 0 7 (by decide +kernel)

theorem test0_complete : Interval test0 0 7 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 7 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0140

/- Original module: RootedQuotaTransfer0140. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0140
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 7 :=
  routeInterval0

theorem disposition_checked (j : Fin 7) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0140.quota
      ((RootedForests.RootedSubsumedForest0296.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0140.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0140.rawLeaves 1 RootedForests.RootedSubsumedForest0140.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0140.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0296.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0140

/- Original module: RootedQuotaTransfer0141Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0141
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 141: use the complete forest for case 297, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0141.quota k ≤ RootedForests.RootedSubsumedForest0297.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0141.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0141.rawLeaves 1 (RootedForests.RootedSubsumedForest0297.rawLeaves i) (routes.get i)

def disposition (j : Fin 18) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0141.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0141

/- Original module: RootedQuotaTransfer0141Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0141
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0141

/- Original module: RootedQuotaTransfer0141. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0141
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 18 :=
  routeInterval0

theorem disposition_checked (j : Fin 18) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0141.quota
      ((RootedForests.RootedSubsumedForest0297.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0141.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0141.rawLeaves 1 RootedForests.RootedSubsumedForest0141.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0141.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0297.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0141

/- Original module: RootedQuotaTransfer0142Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0142
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 142: use the complete forest for case 298, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0142.quota k ≤ RootedForests.RootedSubsumedForest0298.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0142.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0142.rawLeaves 1 (RootedForests.RootedSubsumedForest0298.rawLeaves i) (routes.get i)

def disposition (j : Fin 43) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0142.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0142

/- Original module: RootedQuotaTransfer0142Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0142
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 43 :=
  interval_of_check test0 32 11 (by decide +kernel)

theorem test0_complete : Interval test0 0 43 :=
  (interval_append test0 0 16 43
  test0_block_0
  (interval_append test0 16 32 43
  test0_block_1
  test0_block_2))
theorem routeInterval0 : Interval routeTest 0 43 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0142

/- Original module: RootedQuotaTransfer0142. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0142
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 43 :=
  routeInterval0

theorem disposition_checked (j : Fin 43) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0142.quota
      ((RootedForests.RootedSubsumedForest0298.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0142.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0142.rawLeaves 1 RootedForests.RootedSubsumedForest0142.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0142.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0298.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0142

/- Original module: RootedQuotaTransfer0143Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0143
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 143: use the complete forest for case 299, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0143.quota k ≤ RootedForests.RootedSubsumedForest0299.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0143.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0143.rawLeaves 1 (RootedForests.RootedSubsumedForest0299.rawLeaves i) (routes.get i)

def disposition (j : Fin 12) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0143.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0143

/- Original module: RootedQuotaTransfer0143Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0143
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 12 :=
  interval_of_check test0 0 12 (by decide +kernel)

theorem test0_complete : Interval test0 0 12 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 12 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0143

/- Original module: RootedQuotaTransfer0143. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0143
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 12 :=
  routeInterval0

theorem disposition_checked (j : Fin 12) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0143.quota
      ((RootedForests.RootedSubsumedForest0299.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0143.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0143.rawLeaves 1 RootedForests.RootedSubsumedForest0143.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0143.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0299.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0143

/- Original module: RootedQuotaTransfer0144Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0144
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 144: use the complete forest for case 300, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0144.quota k ≤ RootedForests.RootedSubsumedForest0300.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0144.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0144.rawLeaves 1 (RootedForests.RootedSubsumedForest0300.rawLeaves i) (routes.get i)

def disposition (j : Fin 6) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0144.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0144

/- Original module: RootedQuotaTransfer0144Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0144
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 6 :=
  interval_of_check test0 0 6 (by decide +kernel)

theorem test0_complete : Interval test0 0 6 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 6 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0144

/- Original module: RootedQuotaTransfer0144. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0144
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 6 :=
  routeInterval0

theorem disposition_checked (j : Fin 6) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0144.quota
      ((RootedForests.RootedSubsumedForest0300.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0144.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0144.rawLeaves 1 RootedForests.RootedSubsumedForest0144.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0144.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0300.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0144

/- Original module: RootedQuotaTransfer0152Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0152
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 152: use the complete forest for case 308, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0152.quota k ≤ RootedForests.RootedSubsumedForest0308.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0152.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0152.rawLeaves 1 (RootedForests.RootedSubsumedForest0308.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0152.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0152

/- Original module: RootedQuotaTransfer0152Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0152
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0152

/- Original module: RootedQuotaTransfer0152. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0152
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0152.quota
      ((RootedForests.RootedSubsumedForest0308.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0152.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0152.rawLeaves 1 RootedForests.RootedSubsumedForest0152.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0152.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0308.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0152

/- Original module: RootedQuotaTransfer0154Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0154
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 154: use the complete forest for case 267, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0154.quota k ≤ RootedForests.RootedSubsumedForest0267.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0154.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0154.rawLeaves 1 (RootedForests.RootedSubsumedForest0267.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0154.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0154

/- Original module: RootedQuotaTransfer0154Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0154
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0154

/- Original module: RootedQuotaTransfer0154. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0154
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0154.quota
      ((RootedForests.RootedSubsumedForest0267.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0154.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0154.rawLeaves 1 RootedForests.RootedSubsumedForest0154.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0154.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0267.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0154

/- Original module: RootedQuotaTransfer0197Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0197
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 197: use the complete forest for case 273, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0197.quota k ≤ RootedForests.RootedSubsumedForest0273.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0197.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0197.rawLeaves 1 (RootedForests.RootedSubsumedForest0273.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0197.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0197

/- Original module: RootedQuotaTransfer0197Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0197
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0197

/- Original module: RootedQuotaTransfer0197. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0197
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0197.quota
      ((RootedForests.RootedSubsumedForest0273.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0197.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0197.rawLeaves 1 RootedForests.RootedSubsumedForest0197.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0197.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0273.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0197

/- Original module: RootedQuotaTransfer0198Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0198
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 198: use the complete forest for case 274, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0198.quota k ≤ RootedForests.RootedSubsumedForest0274.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0198.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0198.rawLeaves 1 (RootedForests.RootedSubsumedForest0274.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0198.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0198

/- Original module: RootedQuotaTransfer0198Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0198
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0198

/- Original module: RootedQuotaTransfer0198. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0198
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0198.quota
      ((RootedForests.RootedSubsumedForest0274.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0198.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0198.rawLeaves 1 RootedForests.RootedSubsumedForest0198.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0198.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0274.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0198

/- Original module: RootedQuotaTransfer0199Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0199
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 199: use the complete forest for case 275, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0199.quota k ≤ RootedForests.RootedSubsumedForest0275.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0199.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0199.rawLeaves 1 (RootedForests.RootedSubsumedForest0275.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0199.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0199

/- Original module: RootedQuotaTransfer0199Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0199
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0199

/- Original module: RootedQuotaTransfer0199. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0199
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0199.quota
      ((RootedForests.RootedSubsumedForest0275.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0199.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0199.rawLeaves 1 RootedForests.RootedSubsumedForest0199.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0199.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0275.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0199

/- Original module: RootedQuotaTransfer0200Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0200
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 200: use the complete forest for case 276, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0200.quota k ≤ RootedForests.RootedSubsumedForest0276.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0200.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0200.rawLeaves 1 (RootedForests.RootedSubsumedForest0276.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0200.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0200

/- Original module: RootedQuotaTransfer0200Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0200
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0200

/- Original module: RootedQuotaTransfer0200. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0200
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0200.quota
      ((RootedForests.RootedSubsumedForest0276.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0200.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0200.rawLeaves 1 RootedForests.RootedSubsumedForest0200.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0200.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0276.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0200

/- Original module: RootedQuotaTransfer0201Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0201
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 201: use the complete forest for case 277, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0201.quota k ≤ RootedForests.RootedSubsumedForest0277.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0201.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0201.rawLeaves 1 (RootedForests.RootedSubsumedForest0277.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0201.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0201

/- Original module: RootedQuotaTransfer0201Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0201
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0201

/- Original module: RootedQuotaTransfer0201. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0201
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0201.quota
      ((RootedForests.RootedSubsumedForest0277.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0201.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0201.rawLeaves 1 RootedForests.RootedSubsumedForest0201.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0201.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0277.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0201

/- Original module: RootedQuotaTransfer0209Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0209
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 209: use the complete forest for case 285, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0209.quota k ≤ RootedForests.RootedSubsumedForest0285.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0209.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0209.rawLeaves 1 (RootedForests.RootedSubsumedForest0285.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0209.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0209

/- Original module: RootedQuotaTransfer0209Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0209
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0209

/- Original module: RootedQuotaTransfer0209. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0209
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0209.quota
      ((RootedForests.RootedSubsumedForest0285.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0209.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0209.rawLeaves 1 RootedForests.RootedSubsumedForest0209.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0209.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0285.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0209

/- Original module: RootedQuotaTransfer0212Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0212
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 212: use the complete forest for case 316, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0212.quota k ≤ RootedForests.RootedSubsumedForest0316.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0212.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0212.rawLeaves 1 (RootedForests.RootedSubsumedForest0316.rawLeaves i) (routes.get i)

def disposition (j : Fin 2) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0212.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0212

/- Original module: RootedQuotaTransfer0212Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0212
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 2 :=
  interval_of_check test0 0 2 (by decide +kernel)

theorem test0_complete : Interval test0 0 2 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 2 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0212

/- Original module: RootedQuotaTransfer0212. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0212
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 2 :=
  routeInterval0

theorem disposition_checked (j : Fin 2) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0212.quota
      ((RootedForests.RootedSubsumedForest0316.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0212.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0212.rawLeaves 1 RootedForests.RootedSubsumedForest0212.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0212.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0316.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0212

/- Original module: RootedQuotaTransfer0238Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0238
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 238: use the complete forest for case 296, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0238.quota k ≤ RootedForests.RootedSubsumedForest0296.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0238.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0238.rawLeaves 1 (RootedForests.RootedSubsumedForest0296.rawLeaves i) (routes.get i)

def disposition (j : Fin 7) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0238.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0238

/- Original module: RootedQuotaTransfer0238Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0238
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 7 :=
  interval_of_check test0 0 7 (by decide +kernel)

theorem test0_complete : Interval test0 0 7 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 7 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0238

/- Original module: RootedQuotaTransfer0238. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0238
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 7 :=
  routeInterval0

theorem disposition_checked (j : Fin 7) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0238.quota
      ((RootedForests.RootedSubsumedForest0296.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0238.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0238.rawLeaves 1 RootedForests.RootedSubsumedForest0238.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0238.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0296.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0238

/- Original module: RootedQuotaTransfer0239Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0239
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 239: use the complete forest for case 297, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0239.quota k ≤ RootedForests.RootedSubsumedForest0297.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0239.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0239.rawLeaves 1 (RootedForests.RootedSubsumedForest0297.rawLeaves i) (routes.get i)

def disposition (j : Fin 18) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0239.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0239

/- Original module: RootedQuotaTransfer0239Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0239
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0239

/- Original module: RootedQuotaTransfer0239. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0239
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 18 :=
  routeInterval0

theorem disposition_checked (j : Fin 18) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0239.quota
      ((RootedForests.RootedSubsumedForest0297.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0239.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0239.rawLeaves 1 RootedForests.RootedSubsumedForest0239.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0239.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0297.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0239

/- Original module: RootedQuotaTransfer0240Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0240
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 240: use the complete forest for case 298, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0240.quota k ≤ RootedForests.RootedSubsumedForest0298.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0240.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0240.rawLeaves 1 (RootedForests.RootedSubsumedForest0298.rawLeaves i) (routes.get i)

def disposition (j : Fin 43) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0240.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0240

/- Original module: RootedQuotaTransfer0240Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0240
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 43 :=
  interval_of_check test0 32 11 (by decide +kernel)

theorem test0_complete : Interval test0 0 43 :=
  (interval_append test0 0 16 43
  test0_block_0
  (interval_append test0 16 32 43
  test0_block_1
  test0_block_2))
theorem routeInterval0 : Interval routeTest 0 43 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0240

/- Original module: RootedQuotaTransfer0240. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0240
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 43 :=
  routeInterval0

theorem disposition_checked (j : Fin 43) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0240.quota
      ((RootedForests.RootedSubsumedForest0298.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0240.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0240.rawLeaves 1 RootedForests.RootedSubsumedForest0240.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0240.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0298.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0240

/- Original module: RootedQuotaTransfer0241Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0241
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 241: use the complete forest for case 299, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0241.quota k ≤ RootedForests.RootedSubsumedForest0299.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0241.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0241.rawLeaves 1 (RootedForests.RootedSubsumedForest0299.rawLeaves i) (routes.get i)

def disposition (j : Fin 12) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0241.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0241

/- Original module: RootedQuotaTransfer0241Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0241
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 12 :=
  interval_of_check test0 0 12 (by decide +kernel)

theorem test0_complete : Interval test0 0 12 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 12 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0241

/- Original module: RootedQuotaTransfer0241. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0241
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 12 :=
  routeInterval0

theorem disposition_checked (j : Fin 12) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0241.quota
      ((RootedForests.RootedSubsumedForest0299.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0241.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0241.rawLeaves 1 RootedForests.RootedSubsumedForest0241.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0241.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0299.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0241

/- Original module: RootedQuotaTransfer0242Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0242
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 242: use the complete forest for case 300, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0242.quota k ≤ RootedForests.RootedSubsumedForest0300.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0242.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0242.rawLeaves 1 (RootedForests.RootedSubsumedForest0300.rawLeaves i) (routes.get i)

def disposition (j : Fin 6) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0242.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0242

/- Original module: RootedQuotaTransfer0242Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0242
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 6 :=
  interval_of_check test0 0 6 (by decide +kernel)

theorem test0_complete : Interval test0 0 6 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 6 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0242

/- Original module: RootedQuotaTransfer0242. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0242
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 6 :=
  routeInterval0

theorem disposition_checked (j : Fin 6) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0242.quota
      ((RootedForests.RootedSubsumedForest0300.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0242.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0242.rawLeaves 1 RootedForests.RootedSubsumedForest0242.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0242.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0300.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0242

/- Original module: RootedQuotaTransfer0250Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0250
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 250: use the complete forest for case 308, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0250.quota k ≤ RootedForests.RootedSubsumedForest0308.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0250.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0250.rawLeaves 1 (RootedForests.RootedSubsumedForest0308.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0250.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0250

/- Original module: RootedQuotaTransfer0250Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0250
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0250

/- Original module: RootedQuotaTransfer0250. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0250
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0250.quota
      ((RootedForests.RootedSubsumedForest0308.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0250.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0250.rawLeaves 1 RootedForests.RootedSubsumedForest0250.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0250.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0308.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0250

/- Original module: RootedQuotaTransfer0252Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0252
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 252: use the complete forest for case 319, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0252.quota k ≤ RootedForests.RootedSubsumedForest0319.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0252.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0252.rawLeaves 1 (RootedForests.RootedSubsumedForest0319.rawLeaves i) (routes.get i)

def disposition (j : Fin 69) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0252.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0252

/- Original module: RootedQuotaTransfer0252Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0252
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

theorem test0_block_4 : Interval test0 64 69 :=
  interval_of_check test0 64 5 (by decide +kernel)

theorem test0_complete : Interval test0 0 69 :=
  (interval_append test0 0 32 69
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 69
  test0_block_2
  (interval_append test0 48 64 69
  test0_block_3
  test0_block_4)))
theorem routeInterval0 : Interval routeTest 0 69 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0252

/- Original module: RootedQuotaTransfer0252. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0252
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 69 :=
  routeInterval0

theorem disposition_checked (j : Fin 69) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0252.quota
      ((RootedForests.RootedSubsumedForest0319.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0252.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0252.rawLeaves 1 RootedForests.RootedSubsumedForest0252.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0252.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0319.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0252

/- Original module: RootedQuotaTransfer0270Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0270
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 270: use the complete forest for case 313, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0270.quota k ≤ RootedForests.RootedSubsumedForest0313.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0270.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0270.rawLeaves 1 (RootedForests.RootedSubsumedForest0313.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0270.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0270

/- Original module: RootedQuotaTransfer0270Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0270
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0270

/- Original module: RootedQuotaTransfer0270. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0270
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0270.quota
      ((RootedForests.RootedSubsumedForest0313.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0270.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0270.rawLeaves 1 RootedForests.RootedSubsumedForest0270.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0270.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0313.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0270

/- Original module: RootedQuotaTransfer0288Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0288
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 288: use the complete forest for case 316, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0288.quota k ≤ RootedForests.RootedSubsumedForest0316.quota k := by
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
(.branch 1
 (.leaf (.reuse 0))
 (.leaf (.reuse 1)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0288.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0288.rawLeaves 2 (RootedForests.RootedSubsumedForest0316.rawLeaves i) (routes.get i)

def disposition (j : Fin 2) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0288.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0288

/- Original module: RootedQuotaTransfer0288Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0288
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 2 :=
  interval_of_check test0 0 2 (by decide +kernel)

theorem test0_complete : Interval test0 0 2 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 2 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0288

/- Original module: RootedQuotaTransfer0288. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0288
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 2 :=
  routeInterval0

theorem disposition_checked (j : Fin 2) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0288.quota
      ((RootedForests.RootedSubsumedForest0316.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0288.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0288.rawLeaves 2 RootedForests.RootedSubsumedForest0288.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0288.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0316.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0288

/- Original module: RootedQuotaTransfer0310Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0310
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 310: use the complete forest for case 319, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0310.quota k ≤ RootedForests.RootedSubsumedForest0319.quota k := by
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
(.branch 34
 (.branch 17
 (.leaf (.quota 1))
 (.branch 25
 (.branch 21
 (.branch 19
 (.leaf (.quota 1))
 (.branch 20
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 23
 (.branch 22
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 40
 (.branch 39
 (.leaf (.quota 1))
 (.leaf (.reuse 3)))
 (.branch 41
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 46
 (.branch 44
 (.leaf (.quota 1))
 (.branch 45
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 48
 (.branch 47
 (.leaf (.reuse 6))
 (.leaf (.quota 1)))
 (.branch 49
 (.leaf (.reuse 7))
 (.leaf (.quota 1))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (.reuse 8))
 (.leaf (.quota 2)))
 (.branch 54
 (.leaf (.reuse 10))
 (.leaf (.reuse 11))))
 (.branch 57
 (.branch 56
 (.leaf (.quota 1))
 (.leaf (.reuse 12)))
 (.branch 58
 (.leaf (.reuse 13))
 (.branch 59
 (.leaf (.reuse 14))
 (.leaf (.quota 1))))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf (.reuse 15))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 66
 (.branch 65
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 67
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0310.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0310.rawLeaves 18 (RootedForests.RootedSubsumedForest0319.rawLeaves i) (routes.get i)

def disposition (j : Fin 69) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0310.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0310

/- Original module: RootedQuotaTransfer0310Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0310
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

theorem test0_block_4 : Interval test0 64 69 :=
  interval_of_check test0 64 5 (by decide +kernel)

theorem test0_complete : Interval test0 0 69 :=
  (interval_append test0 0 32 69
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 69
  test0_block_2
  (interval_append test0 48 64 69
  test0_block_3
  test0_block_4)))
theorem routeInterval0 : Interval routeTest 0 69 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0310

/- Original module: RootedQuotaTransfer0310. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0310
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 69 :=
  routeInterval0

theorem disposition_checked (j : Fin 69) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0310.quota
      ((RootedForests.RootedSubsumedForest0319.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0310.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0310.rawLeaves 18 RootedForests.RootedSubsumedForest0310.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0310.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0319.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0310

/- Original module: RootedQuotaTransfer0322Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0322
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 322: use the complete forest for case 331, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0322.quota k ≤ RootedForests.RootedSubsumedForest0331.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0322.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0322.rawLeaves 1 (RootedForests.RootedSubsumedForest0331.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0322.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0322

/- Original module: RootedQuotaTransfer0322Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0322
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0322

/- Original module: RootedQuotaTransfer0322. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0322
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0322.quota
      ((RootedForests.RootedSubsumedForest0331.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0322.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0322.rawLeaves 1 RootedForests.RootedSubsumedForest0322.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0322.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0331.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0322

/- Original module: RootedQuotaTransfer0323Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0323
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 323: use the complete forest for case 328, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0323.quota k ≤ RootedForests.RootedSubsumedForest0328.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0323.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0323.rawLeaves 1 (RootedForests.RootedSubsumedForest0328.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0323.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0323

/- Original module: RootedQuotaTransfer0323Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0323
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0323

/- Original module: RootedQuotaTransfer0323. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0323
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0323.quota
      ((RootedForests.RootedSubsumedForest0328.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0323.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0323.rawLeaves 1 RootedForests.RootedSubsumedForest0323.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0323.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0328.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0323

/- Original module: RootedQuotaTransfer0324Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0324
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 324: use the complete forest for case 334, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0324.quota k ≤ RootedForests.RootedSubsumedForest0334.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0324.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0324.rawLeaves 1 (RootedForests.RootedSubsumedForest0334.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0324.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0324

/- Original module: RootedQuotaTransfer0324Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0324
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0324

/- Original module: RootedQuotaTransfer0324. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0324
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0324.quota
      ((RootedForests.RootedSubsumedForest0334.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0324.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0324.rawLeaves 1 RootedForests.RootedSubsumedForest0324.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0324.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0334.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0324

/- Original module: RootedQuotaTransfer0325Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0325
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 325: use the complete forest for case 331, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0325.quota k ≤ RootedForests.RootedSubsumedForest0331.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0325.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0325.rawLeaves 1 (RootedForests.RootedSubsumedForest0331.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0325.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0325

/- Original module: RootedQuotaTransfer0325Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0325
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0325

/- Original module: RootedQuotaTransfer0325. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0325
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0325.quota
      ((RootedForests.RootedSubsumedForest0331.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0325.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0325.rawLeaves 1 RootedForests.RootedSubsumedForest0325.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0325.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0331.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0325

/- Original module: RootedQuotaTransfer0326Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0326
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 326: use the complete forest for case 337, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0326.quota k ≤ RootedForests.RootedSubsumedForest0337.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0326.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0326.rawLeaves 1 (RootedForests.RootedSubsumedForest0337.rawLeaves i) (routes.get i)

def disposition (j : Fin 145) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0326.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0326

/- Original module: RootedQuotaTransfer0326Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0326
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0326

/- Original module: RootedQuotaTransfer0326Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0326
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 17 :=
  interval_of_check test128 16 1 (by decide +kernel)

theorem test128_complete : Interval test128 0 17 :=
  (interval_append test128 0 16 17
  test128_block_0
  test128_block_1)
theorem routeInterval128 : Interval routeTest 128 145 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0326

/- Original module: RootedQuotaTransfer0326. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0326
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 145 :=
  (interval_append routeTest 0 128 145
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 145) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0326.quota
      ((RootedForests.RootedSubsumedForest0337.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0326.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0326.rawLeaves 1 RootedForests.RootedSubsumedForest0326.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0326.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0337.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0326

/- Original module: RootedQuotaTransfer0327Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0327
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 327: use the complete forest for case 334, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0327.quota k ≤ RootedForests.RootedSubsumedForest0334.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0327.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0327.rawLeaves 1 (RootedForests.RootedSubsumedForest0334.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0327.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0327

/- Original module: RootedQuotaTransfer0327Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0327
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0327

/- Original module: RootedQuotaTransfer0327. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0327
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0327.quota
      ((RootedForests.RootedSubsumedForest0334.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0327.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0327.rawLeaves 1 RootedForests.RootedSubsumedForest0327.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0327.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0334.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0327

/- Original module: RootedQuotaTransfer0329Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0329
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 329: use the complete forest for case 334, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0329.quota k ≤ RootedForests.RootedSubsumedForest0334.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0329.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0329.rawLeaves 1 (RootedForests.RootedSubsumedForest0334.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0329.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0329

/- Original module: RootedQuotaTransfer0329Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0329
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0329

/- Original module: RootedQuotaTransfer0329. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0329
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0329.quota
      ((RootedForests.RootedSubsumedForest0334.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0329.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0329.rawLeaves 1 RootedForests.RootedSubsumedForest0329.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0329.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0334.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0329

/- Original module: RootedQuotaTransfer0330Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0330
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 330: use the complete forest for case 339, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0330.quota k ≤ RootedForests.RootedSubsumedForest0339.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0330.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0330.rawLeaves 1 (RootedForests.RootedSubsumedForest0339.rawLeaves i) (routes.get i)

def disposition (j : Fin 29) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0330.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0330

/- Original module: RootedQuotaTransfer0330Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0330
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0330

/- Original module: RootedQuotaTransfer0330. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0330
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 29 :=
  routeInterval0

theorem disposition_checked (j : Fin 29) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0330.quota
      ((RootedForests.RootedSubsumedForest0339.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0330.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0330.rawLeaves 1 RootedForests.RootedSubsumedForest0330.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0330.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0339.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0330

/- Original module: RootedQuotaTransfer0332Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0332
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 332: use the complete forest for case 337, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0332.quota k ≤ RootedForests.RootedSubsumedForest0337.quota k := by
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
(.branch 72
 (.branch 36
 (.leaf (.quota 1))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.leaf (.quota 1))
 (.branch 39
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 108
 (.branch 90
 (.branch 81
 (.branch 76
 (.leaf (.quota 1))
 (.branch 78
 (.leaf (.quota 1))
 (.branch 79
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 126
 (.leaf (.quota 1))
 (.branch 135
 (.branch 130
 (.leaf (.quota 1))
 (.branch 132
 (.leaf (.quota 1))
 (.branch 133
 (.leaf (.reuse 2))
 (.branch 134
 (.leaf (.reuse 3))
 (.leaf (.quota 1))))))
 (.branch 140
 (.branch 137
 (.leaf (.quota 1))
 (.branch 138
 (.leaf (.quota 1))
 (.branch 139
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0332.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0332.rawLeaves 5 (RootedForests.RootedSubsumedForest0337.rawLeaves i) (routes.get i)

def disposition (j : Fin 145) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0332.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0332

/- Original module: RootedQuotaTransfer0332Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0332
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0332

/- Original module: RootedQuotaTransfer0332Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0332
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 17 :=
  interval_of_check test128 16 1 (by decide +kernel)

theorem test128_complete : Interval test128 0 17 :=
  (interval_append test128 0 16 17
  test128_block_0
  test128_block_1)
theorem routeInterval128 : Interval routeTest 128 145 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0332

/- Original module: RootedQuotaTransfer0332. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0332
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 145 :=
  (interval_append routeTest 0 128 145
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 145) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0332.quota
      ((RootedForests.RootedSubsumedForest0337.rawLeaves j.val).map RootedCaches.RootedSixBase00.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0332.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0332.rawLeaves 5 RootedForests.RootedSubsumedForest0332.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0332.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0337.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0332

/- Original module: RootedQuotaTransfer0333Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0333
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 333: use the complete forest for case 338, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0333.quota k ≤ RootedForests.RootedSubsumedForest0338.quota k := by
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
(.branch 191
 (.branch 95
 (.leaf (.quota 1))
 (.branch 143
 (.branch 119
 (.leaf (.quota 1))
 (.branch 131
 (.branch 125
 (.leaf (.quota 1))
 (.branch 128
 (.branch 126
 (.leaf (.quota 1))
 (.branch 127
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 137
 (.leaf (.quota 1))
 (.branch 140
 (.branch 138
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 167
 (.branch 155
 (.branch 149
 (.leaf (.quota 1))
 (.branch 152
 (.branch 150
 (.leaf (.quota 1))
 (.branch 151
 (.leaf (.reuse 2))
 (.leaf (.quota 1))))
 (.branch 153
 (.leaf (.quota 1))
 (.branch 154
 (.leaf (.quota 1))
 (.leaf (.reuse 3))))))
 (.branch 161
 (.leaf (.quota 1))
 (.branch 164
 (.leaf (.quota 1))
 (.branch 165
 (.leaf (.quota 1))
 (.branch 166
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 179
 (.leaf (.quota 1))
 (.branch 185
 (.branch 182
 (.branch 180
 (.leaf (.quota 2))
 (.branch 181
 (.leaf (.reuse 6))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 287
 (.branch 239
 (.branch 215
 (.branch 203
 (.branch 197
 (.branch 194
 (.leaf (.quota 1))
 (.branch 195
 (.leaf (.reuse 7))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 335
 (.branch 311
 (.branch 299
 (.leaf (.quota 1))
 (.branch 305
 (.branch 302
 (.branch 300
 (.leaf (.quota 1))
 (.branch 301
 (.leaf (.quota 1))
 (.leaf (.reuse 8))))
 (.branch 303
 (.leaf (.reuse 9))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 359
 (.branch 347
 (.leaf (.quota 1))
 (.branch 353
 (.branch 350
 (.branch 348
 (.leaf (.quota 1))
 (.branch 349
 (.leaf (.quota 1))
 (.leaf (.reuse 10))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0333.quota RootedCaches.RootedSixBase00.rawCells
    RootedForests.RootedSubsumedForest0333.rawLeaves 11 (RootedForests.RootedSubsumedForest0338.rawLeaves i) (routes.get i)

def disposition (j : Fin 383) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0333.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0333

/- Original module: RootedQuotaTransfer0333Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0333
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0333

/- Original module: RootedQuotaTransfer0333Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0333
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0333
