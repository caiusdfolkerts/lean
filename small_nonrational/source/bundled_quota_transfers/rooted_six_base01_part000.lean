module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0134Dispositions
public import RootedSubsumedForest0232Data
public import RootedSubsumedForest0135Dispositions
public import RootedSubsumedForest0233Data
public import RootedSubsumedForest0136Dispositions
public import RootedSubsumedForest0234Data
public import RootedSubsumedForest0137Dispositions
public import RootedSubsumedForest0235Data
public import RootedSubsumedForest0145Dispositions
public import RootedSubsumedForest0301Data
public import RootedSubsumedForest0146Dispositions
public import RootedSubsumedForest0302Data
public import RootedSubsumedForest0147Dispositions
public import RootedSubsumedForest0303Data
public import RootedSubsumedForest0148Dispositions
public import RootedSubsumedForest0304Data
public import RootedSubsumedForest0153Dispositions
public import RootedSubsumedForest0309Data
public import RootedSubsumedForest0155Dispositions
public import RootedSubsumedForest0268Data
public import RootedSubsumedForest0202Dispositions
public import RootedSubsumedForest0278Data
public import RootedSubsumedForest0203Dispositions
public import RootedSubsumedForest0279Data
public import RootedSubsumedForest0204Dispositions
public import RootedSubsumedForest0280Data
public import RootedSubsumedForest0205Dispositions
public import RootedSubsumedForest0281Data
public import RootedSubsumedForest0210Dispositions
public import RootedSubsumedForest0286Data
public import RootedSubsumedForest0213Dispositions
public import RootedSubsumedForest0317Data
public import RootedSubsumedForest0225Dispositions
public import RootedSubsumedForest0294Data
public import RootedSubsumedForest0243Dispositions
public import RootedSubsumedForest0244Dispositions
public import RootedSubsumedForest0245Dispositions
public import RootedSubsumedForest0246Dispositions
public import RootedSubsumedForest0251Dispositions
public import RootedSubsumedForest0253Dispositions
public import RootedSubsumedForest0320Data
public import RootedSubsumedForest0271Dispositions
public import RootedSubsumedForest0314Data
public import RootedSubsumedForest0289Dispositions
public import RootedSubsumedForest0311Dispositions

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0134Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0134
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 134: use the complete forest for case 232, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0134.quota k ≤ RootedForests.RootedSubsumedForest0232.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0134.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0134.rawLeaves 1 (RootedForests.RootedSubsumedForest0232.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0134.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0134

/- Original module: RootedQuotaTransfer0134Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0134
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0134

/- Original module: RootedQuotaTransfer0134. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0134
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0134.quota
      ((RootedForests.RootedSubsumedForest0232.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0134.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0134.rawLeaves 1 RootedForests.RootedSubsumedForest0134.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0134.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0232.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0134

/- Original module: RootedQuotaTransfer0135Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0135
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 135: use the complete forest for case 233, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0135.quota k ≤ RootedForests.RootedSubsumedForest0233.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0135.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0135.rawLeaves 1 (RootedForests.RootedSubsumedForest0233.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0135.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0135

/- Original module: RootedQuotaTransfer0135Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0135
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0135

/- Original module: RootedQuotaTransfer0135. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0135
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0135.quota
      ((RootedForests.RootedSubsumedForest0233.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0135.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0135.rawLeaves 1 RootedForests.RootedSubsumedForest0135.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0135.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0233.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0135

/- Original module: RootedQuotaTransfer0136Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0136
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 136: use the complete forest for case 234, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0136.quota k ≤ RootedForests.RootedSubsumedForest0234.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0136.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0136.rawLeaves 1 (RootedForests.RootedSubsumedForest0234.rawLeaves i) (routes.get i)

def disposition (j : Fin 2) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0136.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0136

/- Original module: RootedQuotaTransfer0136Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0136
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0136

/- Original module: RootedQuotaTransfer0136. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0136
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 2 :=
  routeInterval0

theorem disposition_checked (j : Fin 2) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0136.quota
      ((RootedForests.RootedSubsumedForest0234.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0136.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0136.rawLeaves 1 RootedForests.RootedSubsumedForest0136.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0136.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0234.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0136

/- Original module: RootedQuotaTransfer0137Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0137
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 137: use the complete forest for case 235, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0137.quota k ≤ RootedForests.RootedSubsumedForest0235.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0137.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0137.rawLeaves 1 (RootedForests.RootedSubsumedForest0235.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0137.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0137

/- Original module: RootedQuotaTransfer0137Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0137
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0137

/- Original module: RootedQuotaTransfer0137. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0137
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0137.quota
      ((RootedForests.RootedSubsumedForest0235.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0137.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0137.rawLeaves 1 RootedForests.RootedSubsumedForest0137.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0137.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0235.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0137

/- Original module: RootedQuotaTransfer0145Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0145
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 145: use the complete forest for case 301, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0145.quota k ≤ RootedForests.RootedSubsumedForest0301.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0145.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0145.rawLeaves 1 (RootedForests.RootedSubsumedForest0301.rawLeaves i) (routes.get i)

def disposition (j : Fin 120) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0145.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0145

/- Original module: RootedQuotaTransfer0145Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0145
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

theorem test0_block_7 : Interval test0 112 120 :=
  interval_of_check test0 112 8 (by decide +kernel)

theorem test0_complete : Interval test0 0 120 :=
  (interval_append test0 0 64 120
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 120
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 120
  test0_block_6
  test0_block_7)))
theorem routeInterval0 : Interval routeTest 0 120 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0145

/- Original module: RootedQuotaTransfer0145. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0145
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 120 :=
  routeInterval0

theorem disposition_checked (j : Fin 120) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0145.quota
      ((RootedForests.RootedSubsumedForest0301.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0145.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0145.rawLeaves 1 RootedForests.RootedSubsumedForest0145.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0145.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0301.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0145

/- Original module: RootedQuotaTransfer0146Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0146
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 146: use the complete forest for case 302, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0146.quota k ≤ RootedForests.RootedSubsumedForest0302.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0146.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0146.rawLeaves 1 (RootedForests.RootedSubsumedForest0302.rawLeaves i) (routes.get i)

def disposition (j : Fin 133) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0146.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0146

/- Original module: RootedQuotaTransfer0146Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0146
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0146

/- Original module: RootedQuotaTransfer0146Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0146
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 5 :=
  interval_of_check test128 0 5 (by decide +kernel)

theorem test128_complete : Interval test128 0 5 :=
  test128_block_0
theorem routeInterval128 : Interval routeTest 128 133 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0146

/- Original module: RootedQuotaTransfer0146. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0146
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 133 :=
  (interval_append routeTest 0 128 133
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 133) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0146.quota
      ((RootedForests.RootedSubsumedForest0302.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0146.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0146.rawLeaves 1 RootedForests.RootedSubsumedForest0146.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0146.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0302.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0146

/- Original module: RootedQuotaTransfer0147Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0147
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 147: use the complete forest for case 303, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0147.quota k ≤ RootedForests.RootedSubsumedForest0303.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0147.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0147.rawLeaves 1 (RootedForests.RootedSubsumedForest0303.rawLeaves i) (routes.get i)

def disposition (j : Fin 105) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0147.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0147

/- Original module: RootedQuotaTransfer0147Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0147
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

theorem test0_block_6 : Interval test0 96 105 :=
  interval_of_check test0 96 9 (by decide +kernel)

theorem test0_complete : Interval test0 0 105 :=
  (interval_append test0 0 48 105
  (interval_append test0 0 16 48
  test0_block_0
  (interval_append test0 16 32 48
  test0_block_1
  test0_block_2))
  (interval_append test0 48 80 105
  (interval_append test0 48 64 80
  test0_block_3
  test0_block_4)
  (interval_append test0 80 96 105
  test0_block_5
  test0_block_6)))
theorem routeInterval0 : Interval routeTest 0 105 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0147

/- Original module: RootedQuotaTransfer0147. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0147
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 105 :=
  routeInterval0

theorem disposition_checked (j : Fin 105) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0147.quota
      ((RootedForests.RootedSubsumedForest0303.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0147.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0147.rawLeaves 1 RootedForests.RootedSubsumedForest0147.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0147.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0303.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0147

/- Original module: RootedQuotaTransfer0148Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0148
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 148: use the complete forest for case 304, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0148.quota k ≤ RootedForests.RootedSubsumedForest0304.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0148.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0148.rawLeaves 1 (RootedForests.RootedSubsumedForest0304.rawLeaves i) (routes.get i)

def disposition (j : Fin 20) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0148.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0148

/- Original module: RootedQuotaTransfer0148Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0148
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 20 :=
  interval_of_check test0 16 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 20 :=
  (interval_append test0 0 16 20
  test0_block_0
  test0_block_1)
theorem routeInterval0 : Interval routeTest 0 20 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0148

/- Original module: RootedQuotaTransfer0148. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0148
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 20 :=
  routeInterval0

theorem disposition_checked (j : Fin 20) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0148.quota
      ((RootedForests.RootedSubsumedForest0304.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0148.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0148.rawLeaves 1 RootedForests.RootedSubsumedForest0148.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0148.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0304.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0148

/- Original module: RootedQuotaTransfer0153Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0153
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 153: use the complete forest for case 309, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0153.quota k ≤ RootedForests.RootedSubsumedForest0309.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0153.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0153.rawLeaves 1 (RootedForests.RootedSubsumedForest0309.rawLeaves i) (routes.get i)

def disposition (j : Fin 10) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0153.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0153

/- Original module: RootedQuotaTransfer0153Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0153
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 10 :=
  interval_of_check test0 0 10 (by decide +kernel)

theorem test0_complete : Interval test0 0 10 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 10 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0153

/- Original module: RootedQuotaTransfer0153. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0153
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 10 :=
  routeInterval0

theorem disposition_checked (j : Fin 10) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0153.quota
      ((RootedForests.RootedSubsumedForest0309.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0153.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0153.rawLeaves 1 RootedForests.RootedSubsumedForest0153.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0153.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0309.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0153

/- Original module: RootedQuotaTransfer0155Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0155
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 155: use the complete forest for case 268, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0155.quota k ≤ RootedForests.RootedSubsumedForest0268.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0155.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0155.rawLeaves 1 (RootedForests.RootedSubsumedForest0268.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0155.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0155

/- Original module: RootedQuotaTransfer0155Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0155
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0155

/- Original module: RootedQuotaTransfer0155. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0155
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0155.quota
      ((RootedForests.RootedSubsumedForest0268.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0155.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0155.rawLeaves 1 RootedForests.RootedSubsumedForest0155.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0155.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0268.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0155

/- Original module: RootedQuotaTransfer0202Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0202
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 202: use the complete forest for case 278, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0202.quota k ≤ RootedForests.RootedSubsumedForest0278.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0202.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0202.rawLeaves 1 (RootedForests.RootedSubsumedForest0278.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0202.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0202

/- Original module: RootedQuotaTransfer0202Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0202
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0202

/- Original module: RootedQuotaTransfer0202. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0202
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0202.quota
      ((RootedForests.RootedSubsumedForest0278.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0202.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0202.rawLeaves 1 RootedForests.RootedSubsumedForest0202.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0202.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0278.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0202

/- Original module: RootedQuotaTransfer0203Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0203
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 203: use the complete forest for case 279, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0203.quota k ≤ RootedForests.RootedSubsumedForest0279.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0203.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0203.rawLeaves 1 (RootedForests.RootedSubsumedForest0279.rawLeaves i) (routes.get i)

def disposition (j : Fin 16) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0203.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0203

/- Original module: RootedQuotaTransfer0203Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0203
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_complete : Interval test0 0 16 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 16 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0203

/- Original module: RootedQuotaTransfer0203. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0203
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 16 :=
  routeInterval0

theorem disposition_checked (j : Fin 16) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0203.quota
      ((RootedForests.RootedSubsumedForest0279.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0203.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0203.rawLeaves 1 RootedForests.RootedSubsumedForest0203.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0203.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0279.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0203

/- Original module: RootedQuotaTransfer0204Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0204
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 204: use the complete forest for case 280, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0204.quota k ≤ RootedForests.RootedSubsumedForest0280.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0204.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0204.rawLeaves 1 (RootedForests.RootedSubsumedForest0280.rawLeaves i) (routes.get i)

def disposition (j : Fin 2) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0204.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0204

/- Original module: RootedQuotaTransfer0204Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0204
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0204

/- Original module: RootedQuotaTransfer0204. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0204
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 2 :=
  routeInterval0

theorem disposition_checked (j : Fin 2) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0204.quota
      ((RootedForests.RootedSubsumedForest0280.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0204.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0204.rawLeaves 1 RootedForests.RootedSubsumedForest0204.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0204.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0280.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0204

/- Original module: RootedQuotaTransfer0205Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0205
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 205: use the complete forest for case 281, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0205.quota k ≤ RootedForests.RootedSubsumedForest0281.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0205.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0205.rawLeaves 1 (RootedForests.RootedSubsumedForest0281.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0205.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0205

/- Original module: RootedQuotaTransfer0205Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0205
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0205

/- Original module: RootedQuotaTransfer0205. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0205
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0205.quota
      ((RootedForests.RootedSubsumedForest0281.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0205.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0205.rawLeaves 1 RootedForests.RootedSubsumedForest0205.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0205.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0281.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0205

/- Original module: RootedQuotaTransfer0210Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0210
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 210: use the complete forest for case 286, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0210.quota k ≤ RootedForests.RootedSubsumedForest0286.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0210.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0210.rawLeaves 1 (RootedForests.RootedSubsumedForest0286.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0210.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0210

/- Original module: RootedQuotaTransfer0210Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0210
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0210

/- Original module: RootedQuotaTransfer0210. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0210
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0210.quota
      ((RootedForests.RootedSubsumedForest0286.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0210.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0210.rawLeaves 1 RootedForests.RootedSubsumedForest0210.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0210.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0286.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0210

/- Original module: RootedQuotaTransfer0213Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0213
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 213: use the complete forest for case 317, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0213.quota k ≤ RootedForests.RootedSubsumedForest0317.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0213.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0213.rawLeaves 1 (RootedForests.RootedSubsumedForest0317.rawLeaves i) (routes.get i)

def disposition (j : Fin 12) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0213.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0213

/- Original module: RootedQuotaTransfer0213Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0213
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0213

/- Original module: RootedQuotaTransfer0213. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0213
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 12 :=
  routeInterval0

theorem disposition_checked (j : Fin 12) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0213.quota
      ((RootedForests.RootedSubsumedForest0317.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0213.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0213.rawLeaves 1 RootedForests.RootedSubsumedForest0213.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0213.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0317.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0213

/- Original module: RootedQuotaTransfer0225Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0225
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 225: use the complete forest for case 294, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0225.quota k ≤ RootedForests.RootedSubsumedForest0294.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0225.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0225.rawLeaves 1 (RootedForests.RootedSubsumedForest0294.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0225.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0225

/- Original module: RootedQuotaTransfer0225Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0225
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0225

/- Original module: RootedQuotaTransfer0225. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0225
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0225.quota
      ((RootedForests.RootedSubsumedForest0294.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0225.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0225.rawLeaves 1 RootedForests.RootedSubsumedForest0225.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0225.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0294.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0225

/- Original module: RootedQuotaTransfer0243Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0243
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 243: use the complete forest for case 301, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0243.quota k ≤ RootedForests.RootedSubsumedForest0301.quota k := by
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
(.branch 60
 (.branch 30
 (.branch 15
 (.leaf (.quota 1))
 (.branch 22
 (.branch 18
 (.leaf (.quota 1))
 (.branch 20
 (.leaf (.quota 1))
 (.branch 21
 (.leaf (.reuse 0))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf (.quota 1))
 (.branch 32
 (.leaf (.quota 1))
 (.leaf (.reuse 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 52
 (.leaf (.quota 1))
 (.branch 56
 (.branch 54
 (.branch 53
 (.leaf (.quota 1))
 (.leaf (.reuse 2)))
 (.branch 55
 (.leaf (.reuse 3))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 90
 (.branch 75
 (.leaf (.quota 1))
 (.branch 82
 (.leaf (.quota 1))
 (.branch 86
 (.leaf (.quota 1))
 (.branch 88
 (.leaf (.quota 1))
 (.branch 89
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.leaf (.quota 1))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0243.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0243.rawLeaves 5 (RootedForests.RootedSubsumedForest0301.rawLeaves i) (routes.get i)

def disposition (j : Fin 120) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0243.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0243

/- Original module: RootedQuotaTransfer0243Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0243
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

theorem test0_block_7 : Interval test0 112 120 :=
  interval_of_check test0 112 8 (by decide +kernel)

theorem test0_complete : Interval test0 0 120 :=
  (interval_append test0 0 64 120
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 120
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 120
  test0_block_6
  test0_block_7)))
theorem routeInterval0 : Interval routeTest 0 120 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0243

/- Original module: RootedQuotaTransfer0243. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0243
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 120 :=
  routeInterval0

theorem disposition_checked (j : Fin 120) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0243.quota
      ((RootedForests.RootedSubsumedForest0301.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0243.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0243.rawLeaves 5 RootedForests.RootedSubsumedForest0243.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0243.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0301.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0243

/- Original module: RootedQuotaTransfer0244Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0244
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 244: use the complete forest for case 302, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0244.quota k ≤ RootedForests.RootedSubsumedForest0302.quota k := by
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
(.branch 66
 (.branch 33
 (.branch 16
 (.branch 8
 (.leaf (.quota 1))
 (.branch 12
 (.leaf (.quota 1))
 (.branch 14
 (.branch 13
 (.leaf (.reuse 0))
 (.leaf (.reuse 1)))
 (.leaf (.quota 1)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (.reuse 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 28
 (.leaf (.quota 1))
 (.branch 30
 (.branch 29
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 49
 (.branch 41
 (.leaf (.quota 1))
 (.branch 45
 (.branch 43
 (.branch 42
 (.leaf (.reuse 4))
 (.leaf (.quota 1)))
 (.branch 44
 (.leaf (.quota 1))
 (.leaf (.reuse 5))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 99
 (.branch 82
 (.branch 74
 (.branch 70
 (.branch 68
 (.branch 67
 (.leaf (.reuse 6))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 90
 (.branch 86
 (.branch 84
 (.branch 83
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0244.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0244.rawLeaves 8 (RootedForests.RootedSubsumedForest0302.rawLeaves i) (routes.get i)

def disposition (j : Fin 133) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0244.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0244

/- Original module: RootedQuotaTransfer0244Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0244
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0244

/- Original module: RootedQuotaTransfer0244Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0244
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 5 :=
  interval_of_check test128 0 5 (by decide +kernel)

theorem test128_complete : Interval test128 0 5 :=
  test128_block_0
theorem routeInterval128 : Interval routeTest 128 133 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0244

/- Original module: RootedQuotaTransfer0244. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0244
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 133 :=
  (interval_append routeTest 0 128 133
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 133) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0244.quota
      ((RootedForests.RootedSubsumedForest0302.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0244.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0244.rawLeaves 8 RootedForests.RootedSubsumedForest0244.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0244.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0302.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0244

/- Original module: RootedQuotaTransfer0245Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0245
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 245: use the complete forest for case 303, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0245.quota k ≤ RootedForests.RootedSubsumedForest0303.quota k := by
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
(.branch 52
 (.branch 26
 (.branch 13
 (.branch 6
 (.leaf (.quota 1))
 (.branch 9
 (.branch 7
 (.leaf (.quota 1))
 (.branch 8
 (.leaf (.reuse 0))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 39
 (.branch 32
 (.leaf (.quota 1))
 (.branch 35
 (.branch 33
 (.leaf (.quota 1))
 (.branch 34
 (.leaf (.reuse 1))
 (.leaf (.reuse 2))))
 (.leaf (.quota 1))))
 (.branch 45
 (.branch 42
 (.leaf (.quota 1))
 (.branch 43
 (.leaf (.quota 1))
 (.branch 44
 (.leaf (.reuse 3))
 (.leaf (.quota 1)))))
 (.branch 48
 (.branch 46
 (.leaf (.reuse 4))
 (.leaf (.quota 1)))
 (.branch 50
 (.branch 49
 (.leaf (.reuse 5))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 78
 (.branch 65
 (.branch 58
 (.branch 55
 (.leaf (.quota 1))
 (.branch 56
 (.leaf (.reuse 6))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 71
 (.leaf (.quota 1))
 (.branch 74
 (.branch 72
 (.leaf (.quota 1))
 (.branch 73
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 76
 (.branch 75
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 91
 (.branch 84
 (.branch 81
 (.leaf (.quota 1))
 (.branch 82
 (.leaf (.reuse 9))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0245.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0245.rawLeaves 10 (RootedForests.RootedSubsumedForest0303.rawLeaves i) (routes.get i)

def disposition (j : Fin 105) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0245.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0245

/- Original module: RootedQuotaTransfer0245Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0245
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

theorem test0_block_6 : Interval test0 96 105 :=
  interval_of_check test0 96 9 (by decide +kernel)

theorem test0_complete : Interval test0 0 105 :=
  (interval_append test0 0 48 105
  (interval_append test0 0 16 48
  test0_block_0
  (interval_append test0 16 32 48
  test0_block_1
  test0_block_2))
  (interval_append test0 48 80 105
  (interval_append test0 48 64 80
  test0_block_3
  test0_block_4)
  (interval_append test0 80 96 105
  test0_block_5
  test0_block_6)))
theorem routeInterval0 : Interval routeTest 0 105 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0245

/- Original module: RootedQuotaTransfer0245. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0245
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 105 :=
  routeInterval0

theorem disposition_checked (j : Fin 105) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0245.quota
      ((RootedForests.RootedSubsumedForest0303.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0245.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0245.rawLeaves 10 RootedForests.RootedSubsumedForest0245.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0245.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0303.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0245

/- Original module: RootedQuotaTransfer0246Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0246
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 246: use the complete forest for case 304, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0246.quota k ≤ RootedForests.RootedSubsumedForest0304.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0246.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0246.rawLeaves 1 (RootedForests.RootedSubsumedForest0304.rawLeaves i) (routes.get i)

def disposition (j : Fin 20) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0246.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0246

/- Original module: RootedQuotaTransfer0246Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0246
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 20 :=
  interval_of_check test0 16 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 20 :=
  (interval_append test0 0 16 20
  test0_block_0
  test0_block_1)
theorem routeInterval0 : Interval routeTest 0 20 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0246

/- Original module: RootedQuotaTransfer0246. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0246
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 20 :=
  routeInterval0

theorem disposition_checked (j : Fin 20) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0246.quota
      ((RootedForests.RootedSubsumedForest0304.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0246.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0246.rawLeaves 1 RootedForests.RootedSubsumedForest0246.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0246.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0304.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0246

/- Original module: RootedQuotaTransfer0251Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0251
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 251: use the complete forest for case 309, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0251.quota k ≤ RootedForests.RootedSubsumedForest0309.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0251.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0251.rawLeaves 1 (RootedForests.RootedSubsumedForest0309.rawLeaves i) (routes.get i)

def disposition (j : Fin 10) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0251.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0251

/- Original module: RootedQuotaTransfer0251Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0251
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 10 :=
  interval_of_check test0 0 10 (by decide +kernel)

theorem test0_complete : Interval test0 0 10 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 10 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0251

/- Original module: RootedQuotaTransfer0251. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0251
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 10 :=
  routeInterval0

theorem disposition_checked (j : Fin 10) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0251.quota
      ((RootedForests.RootedSubsumedForest0309.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0251.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0251.rawLeaves 1 RootedForests.RootedSubsumedForest0251.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0251.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0309.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0251

/- Original module: RootedQuotaTransfer0253Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0253
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 253: use the complete forest for case 320, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0253.quota k ≤ RootedForests.RootedSubsumedForest0320.quota k := by
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
 (.leaf (.quota 1))
 (.branch 72
 (.branch 60
 (.branch 54
 (.leaf (.quota 1))
 (.branch 57
 (.leaf (.quota 1))
 (.branch 58
 (.leaf (.quota 1))
 (.branch 59
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.leaf (.quota 1)))
 (.branch 84
 (.branch 78
 (.leaf (.quota 1))
 (.branch 81
 (.branch 79
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0253.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0253.rawLeaves 2 (RootedForests.RootedSubsumedForest0320.rawLeaves i) (routes.get i)

def disposition (j : Fin 192) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0253.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0253

/- Original module: RootedQuotaTransfer0253Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0253
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0253

/- Original module: RootedQuotaTransfer0253Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0253
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0253

/- Original module: RootedQuotaTransfer0253. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0253
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 192 :=
  (interval_append routeTest 0 128 192
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 192) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0253.quota
      ((RootedForests.RootedSubsumedForest0320.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0253.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0253.rawLeaves 2 RootedForests.RootedSubsumedForest0253.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0253.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0320.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0253

/- Original module: RootedQuotaTransfer0271Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0271
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 271: use the complete forest for case 314, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0271.quota k ≤ RootedForests.RootedSubsumedForest0314.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0271.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0271.rawLeaves 1 (RootedForests.RootedSubsumedForest0314.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0271.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0271

/- Original module: RootedQuotaTransfer0271Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0271
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0271

/- Original module: RootedQuotaTransfer0271. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0271
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0271.quota
      ((RootedForests.RootedSubsumedForest0314.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0271.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0271.rawLeaves 1 RootedForests.RootedSubsumedForest0271.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0271.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0314.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0271

/- Original module: RootedQuotaTransfer0289Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0289
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 289: use the complete forest for case 317, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0289.quota k ≤ RootedForests.RootedSubsumedForest0317.quota k := by
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
(.branch 6
 (.leaf (.quota 1))
 (.branch 9
 (.branch 7
 (.leaf (.quota 2))
 (.branch 8
 (.leaf (.quota 1))
 (.leaf (.reuse 1))))
 (.branch 10
 (.leaf (.reuse 2))
 (.leaf (.quota 1)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0289.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0289.rawLeaves 3 (RootedForests.RootedSubsumedForest0317.rawLeaves i) (routes.get i)

def disposition (j : Fin 12) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0289.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0289

/- Original module: RootedQuotaTransfer0289Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0289
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0289

/- Original module: RootedQuotaTransfer0289. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0289
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 12 :=
  routeInterval0

theorem disposition_checked (j : Fin 12) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0289.quota
      ((RootedForests.RootedSubsumedForest0317.rawLeaves j.val).map RootedCaches.RootedSixBase01.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0289.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0289.rawLeaves 3 RootedForests.RootedSubsumedForest0289.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0289.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0317.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0289

/- Original module: RootedQuotaTransfer0311Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0311
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 311: use the complete forest for case 320, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0311.quota k ≤ RootedForests.RootedSubsumedForest0320.quota k := by
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
 (.branch 3
 (.branch 1
 (.leaf (.quota 1))
 (.branch 2
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf (.quota 1))
 (.branch 26
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.leaf (.quota 1)))
 (.branch 33
 (.leaf (.quota 1))
 (.branch 34
 (.leaf (.quota 1))
 (.branch 35
 (.leaf (.quota 1))
 (.leaf (.quota 3))))))
 (.branch 42
 (.leaf (.quota 1))
 (.branch 45
 (.branch 43
 (.leaf (.quota 1))
 (.branch 44
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 46
 (.leaf (.quota 1))
 (.branch 47
 (.leaf (.quota 1))
 (.leaf (.reuse 4))))))))
 (.branch 72
 (.branch 60
 (.branch 54
 (.leaf (.quota 1))
 (.branch 57
 (.leaf (.quota 1))
 (.branch 58
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 66
 (.branch 63
 (.branch 61
 (.leaf (.quota 2))
 (.branch 62
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 69
 (.leaf (.quota 1))
 (.branch 70
 (.leaf (.quota 1))
 (.branch 71
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 84
 (.branch 78
 (.branch 75
 (.branch 73
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 76
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 81
 (.branch 79
 (.leaf (.quota 1))
 (.branch 80
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 82
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 90
 (.leaf (.quota 1))
 (.branch 93
 (.branch 91
 (.leaf (.quota 1))
 (.branch 92
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))))
 (.branch 144
 (.branch 120
 (.branch 108
 (.branch 102
 (.branch 99
 (.branch 97
 (.leaf (.quota 1))
 (.branch 98
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 105
 (.branch 103
 (.leaf (.quota 2))
 (.branch 104
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 106
 (.leaf (.quota 1))
 (.branch 107
 (.leaf (.quota 1))
 (.leaf (.reuse 19))))))
 (.branch 114
 (.branch 111
 (.branch 109
 (.leaf (.reuse 20))
 (.branch 110
 (.leaf (.quota 1))
 (.leaf (.reuse 21))))
 (.branch 112
 (.leaf (.reuse 22))
 (.branch 113
 (.leaf (.quota 1))
 (.leaf (.reuse 23)))))
 (.branch 117
 (.branch 115
 (.leaf (.reuse 24))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 132
 (.branch 126
 (.branch 123
 (.leaf (.quota 1))
 (.branch 124
 (.leaf (.quota 1))
 (.branch 125
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 129
 (.leaf (.quota 1))
 (.branch 130
 (.leaf (.quota 1))
 (.branch 131
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 138
 (.branch 135
 (.branch 133
 (.leaf (.quota 1))
 (.branch 134
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 141
 (.branch 139
 (.leaf (.quota 1))
 (.branch 140
 (.leaf (.reuse 28))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 168
 (.branch 156
 (.branch 150
 (.branch 147
 (.branch 145
 (.leaf (.quota 1))
 (.branch 146
 (.leaf (.quota 1))
 (.leaf (.reuse 29))))
 (.branch 148
 (.leaf (.reuse 30))
 (.leaf (.quota 1))))
 (.branch 153
 (.branch 151
 (.leaf (.quota 1))
 (.branch 152
 (.leaf (.quota 1))
 (.leaf (.reuse 31))))
 (.branch 154
 (.leaf (.quota 1))
 (.branch 155
 (.leaf (.reuse 32))
 (.leaf (.quota 1))))))
 (.branch 162
 (.branch 159
 (.branch 157
 (.leaf (.quota 1))
 (.branch 158
 (.leaf (.reuse 33))
 (.leaf (.quota 1))))
 (.branch 160
 (.leaf (.reuse 34))
 (.leaf (.quota 1))))
 (.branch 165
 (.leaf (.quota 1))
 (.branch 166
 (.leaf (.quota 1))
 (.branch 167
 (.leaf (.reuse 35))
 (.leaf (.reuse 36)))))))
 (.branch 180
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf (.reuse 37))
 (.leaf (.quota 1)))
 (.branch 172
 (.leaf (.quota 1))
 (.branch 173
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 177
 (.leaf (.quota 1))
 (.branch 178
 (.leaf (.quota 1))
 (.branch 179
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 186
 (.branch 183
 (.branch 181
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 189
 (.leaf (.quota 1))
 (.branch 190
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0311.quota RootedCaches.RootedSixBase01.rawCells
    RootedForests.RootedSubsumedForest0311.rawLeaves 42 (RootedForests.RootedSubsumedForest0320.rawLeaves i) (routes.get i)

def disposition (j : Fin 192) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0311.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0311
