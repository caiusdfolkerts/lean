module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0138Dispositions
public import RootedSubsumedForest0236Data
public import RootedSubsumedForest0139Dispositions
public import RootedSubsumedForest0237Data
public import RootedSubsumedForest0149Dispositions
public import RootedSubsumedForest0305Data
public import RootedSubsumedForest0150Dispositions
public import RootedSubsumedForest0306Data
public import RootedSubsumedForest0151Dispositions
public import RootedSubsumedForest0307Data
public import RootedSubsumedForest0156Dispositions
public import RootedSubsumedForest0269Data
public import RootedSubsumedForest0206Dispositions
public import RootedSubsumedForest0282Data
public import RootedSubsumedForest0207Dispositions
public import RootedSubsumedForest0283Data
public import RootedSubsumedForest0208Dispositions
public import RootedSubsumedForest0284Data
public import RootedSubsumedForest0211Dispositions
public import RootedSubsumedForest0287Data
public import RootedSubsumedForest0214Dispositions
public import RootedSubsumedForest0318Data
public import RootedSubsumedForest0226Dispositions
public import RootedSubsumedForest0295Data
public import RootedSubsumedForest0247Dispositions
public import RootedSubsumedForest0248Dispositions
public import RootedSubsumedForest0249Dispositions
public import RootedSubsumedForest0254Dispositions
public import RootedSubsumedForest0321Data
public import RootedSubsumedForest0272Dispositions
public import RootedSubsumedForest0315Data
public import RootedSubsumedForest0290Dispositions
public import RootedSubsumedForest0312Dispositions
public import RootedSubsumedForest0356Dispositions
public import RootedSubsumedForest0361Data
public import RootedSubsumedForest0357Dispositions
public import RootedSubsumedForest0358Dispositions
public import RootedSubsumedForest0359Dispositions
public import RootedSubsumedForest0365Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0138Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0138
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 138: use the complete forest for case 236, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0138.quota k ≤ RootedForests.RootedSubsumedForest0236.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0138.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0138.rawLeaves 1 (RootedForests.RootedSubsumedForest0236.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0138.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0138

/- Original module: RootedQuotaTransfer0138Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0138
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0138

/- Original module: RootedQuotaTransfer0138. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0138
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0138.quota
      ((RootedForests.RootedSubsumedForest0236.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0138.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0138.rawLeaves 1 RootedForests.RootedSubsumedForest0138.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0138.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0236.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0138

/- Original module: RootedQuotaTransfer0139Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0139
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 139: use the complete forest for case 237, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0139.quota k ≤ RootedForests.RootedSubsumedForest0237.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0139.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0139.rawLeaves 1 (RootedForests.RootedSubsumedForest0237.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0139.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0139

/- Original module: RootedQuotaTransfer0139Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0139
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0139

/- Original module: RootedQuotaTransfer0139. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0139
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0139.quota
      ((RootedForests.RootedSubsumedForest0237.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0139.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0139.rawLeaves 1 RootedForests.RootedSubsumedForest0139.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0139.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0237.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0139

/- Original module: RootedQuotaTransfer0149Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0149
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 149: use the complete forest for case 305, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0149.quota k ≤ RootedForests.RootedSubsumedForest0305.quota k := by
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
(.branch 46
 (.leaf (.quota 1))
 (.branch 69
 (.branch 57
 (.leaf (.quota 1))
 (.branch 63
 (.branch 60
 (.leaf (.quota 1))
 (.branch 61
 (.leaf (.reuse 0))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0149.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0149.rawLeaves 1 (RootedForests.RootedSubsumedForest0305.rawLeaves i) (routes.get i)

def disposition (j : Fin 93) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0149.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0149

/- Original module: RootedQuotaTransfer0149Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0149
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

theorem test0_block_5 : Interval test0 80 93 :=
  interval_of_check test0 80 13 (by decide +kernel)

theorem test0_complete : Interval test0 0 93 :=
  (interval_append test0 0 48 93
  (interval_append test0 0 16 48
  test0_block_0
  (interval_append test0 16 32 48
  test0_block_1
  test0_block_2))
  (interval_append test0 48 64 93
  test0_block_3
  (interval_append test0 64 80 93
  test0_block_4
  test0_block_5)))
theorem routeInterval0 : Interval routeTest 0 93 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0149

/- Original module: RootedQuotaTransfer0149. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0149
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 93 :=
  routeInterval0

theorem disposition_checked (j : Fin 93) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0149.quota
      ((RootedForests.RootedSubsumedForest0305.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0149.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0149.rawLeaves 1 RootedForests.RootedSubsumedForest0149.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0149.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0305.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0149

/- Original module: RootedQuotaTransfer0150Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0150
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 150: use the complete forest for case 306, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0150.quota k ≤ RootedForests.RootedSubsumedForest0306.quota k := by
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
(.branch 59
 (.branch 29
 (.leaf (.quota 1))
 (.branch 44
 (.branch 36
 (.leaf (.quota 1))
 (.branch 40
 (.branch 38
 (.leaf (.quota 1))
 (.branch 39
 (.leaf (.quota 1))
 (.leaf (.reuse 0))))
 (.leaf (.quota 1))))
 (.branch 51
 (.branch 47
 (.branch 45
 (.leaf (.quota 1))
 (.branch 46
 (.leaf (.reuse 1))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0150.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0150.rawLeaves 2 (RootedForests.RootedSubsumedForest0306.rawLeaves i) (routes.get i)

def disposition (j : Fin 119) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0150.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0150

/- Original module: RootedQuotaTransfer0150Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0150
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

theorem test0_block_7 : Interval test0 112 119 :=
  interval_of_check test0 112 7 (by decide +kernel)

theorem test0_complete : Interval test0 0 119 :=
  (interval_append test0 0 64 119
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 119
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 119
  test0_block_6
  test0_block_7)))
theorem routeInterval0 : Interval routeTest 0 119 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0150

/- Original module: RootedQuotaTransfer0150. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0150
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 119 :=
  routeInterval0

theorem disposition_checked (j : Fin 119) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0150.quota
      ((RootedForests.RootedSubsumedForest0306.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0150.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0150.rawLeaves 2 RootedForests.RootedSubsumedForest0150.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0150.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0306.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0150

/- Original module: RootedQuotaTransfer0151Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0151
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 151: use the complete forest for case 307, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0151.quota k ≤ RootedForests.RootedSubsumedForest0307.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0151.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0151.rawLeaves 1 (RootedForests.RootedSubsumedForest0307.rawLeaves i) (routes.get i)

def disposition (j : Fin 25) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0151.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0151

/- Original module: RootedQuotaTransfer0151Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0151
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0151

/- Original module: RootedQuotaTransfer0151. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0151
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 25 :=
  routeInterval0

theorem disposition_checked (j : Fin 25) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0151.quota
      ((RootedForests.RootedSubsumedForest0307.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0151.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0151.rawLeaves 1 RootedForests.RootedSubsumedForest0151.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0151.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0307.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0151

/- Original module: RootedQuotaTransfer0156Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0156
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 156: use the complete forest for case 269, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0156.quota k ≤ RootedForests.RootedSubsumedForest0269.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0156.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0156.rawLeaves 1 (RootedForests.RootedSubsumedForest0269.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0156.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0156

/- Original module: RootedQuotaTransfer0156Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0156
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0156

/- Original module: RootedQuotaTransfer0156. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0156
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0156.quota
      ((RootedForests.RootedSubsumedForest0269.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0156.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0156.rawLeaves 1 RootedForests.RootedSubsumedForest0156.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0156.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0269.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0156

/- Original module: RootedQuotaTransfer0206Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0206
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 206: use the complete forest for case 282, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0206.quota k ≤ RootedForests.RootedSubsumedForest0282.quota k := by
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
 (.leaf (.reuse 0))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0206.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0206.rawLeaves 1 (RootedForests.RootedSubsumedForest0282.rawLeaves i) (routes.get i)

def disposition (j : Fin 12) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0206.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0206

/- Original module: RootedQuotaTransfer0206Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0206
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0206

/- Original module: RootedQuotaTransfer0206. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0206
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 12 :=
  routeInterval0

theorem disposition_checked (j : Fin 12) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0206.quota
      ((RootedForests.RootedSubsumedForest0282.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0206.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0206.rawLeaves 1 RootedForests.RootedSubsumedForest0206.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0206.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0282.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0206

/- Original module: RootedQuotaTransfer0207Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0207
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 207: use the complete forest for case 283, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0207.quota k ≤ RootedForests.RootedSubsumedForest0283.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0207.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0207.rawLeaves 1 (RootedForests.RootedSubsumedForest0283.rawLeaves i) (routes.get i)

def disposition (j : Fin 7) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0207.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0207

/- Original module: RootedQuotaTransfer0207Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0207
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0207

/- Original module: RootedQuotaTransfer0207. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0207
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 7 :=
  routeInterval0

theorem disposition_checked (j : Fin 7) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0207.quota
      ((RootedForests.RootedSubsumedForest0283.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0207.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0207.rawLeaves 1 RootedForests.RootedSubsumedForest0207.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0207.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0283.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0207

/- Original module: RootedQuotaTransfer0208Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0208
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 208: use the complete forest for case 284, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0208.quota k ≤ RootedForests.RootedSubsumedForest0284.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0208.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0208.rawLeaves 1 (RootedForests.RootedSubsumedForest0284.rawLeaves i) (routes.get i)

def disposition (j : Fin 2) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0208.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0208

/- Original module: RootedQuotaTransfer0208Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0208
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0208

/- Original module: RootedQuotaTransfer0208. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0208
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 2 :=
  routeInterval0

theorem disposition_checked (j : Fin 2) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0208.quota
      ((RootedForests.RootedSubsumedForest0284.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0208.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0208.rawLeaves 1 RootedForests.RootedSubsumedForest0208.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0208.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0284.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0208

/- Original module: RootedQuotaTransfer0211Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0211
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 211: use the complete forest for case 287, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0211.quota k ≤ RootedForests.RootedSubsumedForest0287.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0211.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0211.rawLeaves 1 (RootedForests.RootedSubsumedForest0287.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0211.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0211

/- Original module: RootedQuotaTransfer0211Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0211
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0211

/- Original module: RootedQuotaTransfer0211. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0211
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0211.quota
      ((RootedForests.RootedSubsumedForest0287.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0211.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0211.rawLeaves 1 RootedForests.RootedSubsumedForest0211.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0211.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0287.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0211

/- Original module: RootedQuotaTransfer0214Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0214
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 214: use the complete forest for case 318, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0214.quota k ≤ RootedForests.RootedSubsumedForest0318.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0214.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0214.rawLeaves 1 (RootedForests.RootedSubsumedForest0318.rawLeaves i) (routes.get i)

def disposition (j : Fin 21) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0214.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0214

/- Original module: RootedQuotaTransfer0214Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0214
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 21 :=
  interval_of_check test0 16 5 (by decide +kernel)

theorem test0_complete : Interval test0 0 21 :=
  (interval_append test0 0 16 21
  test0_block_0
  test0_block_1)
theorem routeInterval0 : Interval routeTest 0 21 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0214

/- Original module: RootedQuotaTransfer0214. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0214
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 21 :=
  routeInterval0

theorem disposition_checked (j : Fin 21) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0214.quota
      ((RootedForests.RootedSubsumedForest0318.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0214.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0214.rawLeaves 1 RootedForests.RootedSubsumedForest0214.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0214.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0318.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0214

/- Original module: RootedQuotaTransfer0226Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0226
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 226: use the complete forest for case 295, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0226.quota k ≤ RootedForests.RootedSubsumedForest0295.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0226.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0226.rawLeaves 1 (RootedForests.RootedSubsumedForest0295.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0226.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0226

/- Original module: RootedQuotaTransfer0226Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0226
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0226

/- Original module: RootedQuotaTransfer0226. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0226
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0226.quota
      ((RootedForests.RootedSubsumedForest0295.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0226.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0226.rawLeaves 1 RootedForests.RootedSubsumedForest0226.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0226.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0295.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0226

/- Original module: RootedQuotaTransfer0247Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0247
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 247: use the complete forest for case 305, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0247.quota k ≤ RootedForests.RootedSubsumedForest0305.quota k := by
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
(.branch 46
 (.branch 23
 (.branch 11
 (.leaf (.quota 1))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf (.quota 1))
 (.branch 13
 (.leaf (.reuse 0))
 (.leaf (.reuse 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf (.quota 1))
 (.branch 36
 (.leaf (.reuse 4))
 (.leaf (.quota 1))))
 (.branch 38
 (.leaf (.quota 1))
 (.branch 39
 (.leaf (.reuse 5))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 69
 (.branch 57
 (.branch 51
 (.leaf (.quota 1))
 (.branch 54
 (.leaf (.quota 1))
 (.branch 55
 (.leaf (.quota 1))
 (.branch 56
 (.leaf (.quota 1))
 (.leaf (.reuse 6))))))
 (.branch 63
 (.leaf (.quota 1))
 (.branch 66
 (.leaf (.quota 1))
 (.branch 67
 (.leaf (.reuse 8))
 (.branch 68
 (.leaf (.reuse 9))
 (.leaf (.reuse 10)))))))
 (.branch 81
 (.leaf (.quota 1))
 (.branch 87
 (.leaf (.quota 1))
 (.branch 90
 (.leaf (.quota 1))
 (.branch 91
 (.leaf (.quota 2))
 (.branch 92
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0247.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0247.rawLeaves 13 (RootedForests.RootedSubsumedForest0305.rawLeaves i) (routes.get i)

def disposition (j : Fin 93) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0247.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0247

/- Original module: RootedQuotaTransfer0247Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0247
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

theorem test0_block_5 : Interval test0 80 93 :=
  interval_of_check test0 80 13 (by decide +kernel)

theorem test0_complete : Interval test0 0 93 :=
  (interval_append test0 0 48 93
  (interval_append test0 0 16 48
  test0_block_0
  (interval_append test0 16 32 48
  test0_block_1
  test0_block_2))
  (interval_append test0 48 64 93
  test0_block_3
  (interval_append test0 64 80 93
  test0_block_4
  test0_block_5)))
theorem routeInterval0 : Interval routeTest 0 93 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0247

/- Original module: RootedQuotaTransfer0247. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0247
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 93 :=
  routeInterval0

theorem disposition_checked (j : Fin 93) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0247.quota
      ((RootedForests.RootedSubsumedForest0305.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0247.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0247.rawLeaves 13 RootedForests.RootedSubsumedForest0247.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0247.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0305.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0247

/- Original module: RootedQuotaTransfer0248Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0248
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 248: use the complete forest for case 306, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0248.quota k ≤ RootedForests.RootedSubsumedForest0306.quota k := by
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
(.branch 59
 (.branch 29
 (.branch 14
 (.leaf (.quota 1))
 (.branch 21
 (.branch 17
 (.leaf (.quota 1))
 (.branch 19
 (.leaf (.quota 1))
 (.branch 20
 (.leaf (.quota 1))
 (.leaf (.reuse 0)))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf (.reuse 1))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 44
 (.leaf (.quota 1))
 (.branch 51
 (.leaf (.quota 1))
 (.branch 55
 (.leaf (.quota 1))
 (.branch 57
 (.branch 56
 (.leaf (.reuse 4))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 89
 (.branch 74
 (.branch 66
 (.branch 62
 (.branch 60
 (.leaf (.quota 1))
 (.branch 61
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 64
 (.branch 63
 (.leaf (.quota 1))
 (.leaf (.reuse 6)))
 (.leaf (.quota 1))))
 (.branch 70
 (.leaf (.quota 1))
 (.branch 72
 (.branch 71
 (.leaf (.reuse 7))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 81
 (.branch 77
 (.leaf (.quota 1))
 (.branch 79
 (.branch 78
 (.leaf (.reuse 8))
 (.leaf (.quota 1)))
 (.branch 80
 (.leaf (.reuse 9))
 (.leaf (.reuse 10)))))
 (.branch 85
 (.branch 83
 (.branch 82
 (.leaf (.reuse 11))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 104
 (.branch 96
 (.branch 92
 (.leaf (.quota 1))
 (.branch 94
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 111
 (.branch 107
 (.leaf (.quota 1))
 (.branch 109
 (.leaf (.quota 1))
 (.branch 110
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 115
 (.branch 113
 (.branch 112
 (.leaf (.reuse 15))
 (.leaf (.reuse 16)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0248.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0248.rawLeaves 17 (RootedForests.RootedSubsumedForest0306.rawLeaves i) (routes.get i)

def disposition (j : Fin 119) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0248.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0248

/- Original module: RootedQuotaTransfer0248Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0248
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

theorem test0_block_7 : Interval test0 112 119 :=
  interval_of_check test0 112 7 (by decide +kernel)

theorem test0_complete : Interval test0 0 119 :=
  (interval_append test0 0 64 119
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 119
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 119
  test0_block_6
  test0_block_7)))
theorem routeInterval0 : Interval routeTest 0 119 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0248

/- Original module: RootedQuotaTransfer0248. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0248
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 119 :=
  routeInterval0

theorem disposition_checked (j : Fin 119) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0248.quota
      ((RootedForests.RootedSubsumedForest0306.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0248.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0248.rawLeaves 17 RootedForests.RootedSubsumedForest0248.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0248.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0306.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0248

/- Original module: RootedQuotaTransfer0249Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0249
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 249: use the complete forest for case 307, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0249.quota k ≤ RootedForests.RootedSubsumedForest0307.quota k := by
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
 (.leaf (.quota 1))
 (.branch 21
 (.branch 19
 (.leaf (.quota 1))
 (.branch 20
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0249.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0249.rawLeaves 1 (RootedForests.RootedSubsumedForest0307.rawLeaves i) (routes.get i)

def disposition (j : Fin 25) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0249.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0249

/- Original module: RootedQuotaTransfer0249Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0249
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0249

/- Original module: RootedQuotaTransfer0249. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0249
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 25 :=
  routeInterval0

theorem disposition_checked (j : Fin 25) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0249.quota
      ((RootedForests.RootedSubsumedForest0307.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0249.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0249.rawLeaves 1 RootedForests.RootedSubsumedForest0249.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0249.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0307.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0249

/- Original module: RootedQuotaTransfer0254Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0254
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 254: use the complete forest for case 321, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0254.quota k ≤ RootedForests.RootedSubsumedForest0321.quota k := by
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
(.branch 68
 (.branch 34
 (.leaf (.quota 1))
 (.branch 51
 (.branch 42
 (.leaf (.quota 1))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 102
 (.leaf (.quota 1))
 (.branch 119
 (.branch 110
 (.leaf (.quota 1))
 (.branch 114
 (.branch 112
 (.leaf (.quota 1))
 (.branch 113
 (.leaf (.reuse 1))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0254.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0254.rawLeaves 2 (RootedForests.RootedSubsumedForest0321.rawLeaves i) (routes.get i)

def disposition (j : Fin 136) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0254.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0254

/- Original module: RootedQuotaTransfer0254Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0254
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0254

/- Original module: RootedQuotaTransfer0254Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0254
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 8 :=
  interval_of_check test128 0 8 (by decide +kernel)

theorem test128_complete : Interval test128 0 8 :=
  test128_block_0
theorem routeInterval128 : Interval routeTest 128 136 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0254

/- Original module: RootedQuotaTransfer0254. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0254
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 136 :=
  (interval_append routeTest 0 128 136
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 136) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0254.quota
      ((RootedForests.RootedSubsumedForest0321.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0254.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0254.rawLeaves 2 RootedForests.RootedSubsumedForest0254.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0254.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0321.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0254

/- Original module: RootedQuotaTransfer0272Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0272
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 272: use the complete forest for case 315, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0272.quota k ≤ RootedForests.RootedSubsumedForest0315.quota k := by
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
(.branch 5
 (.leaf (.quota 1))
 (.branch 7
 (.leaf (.quota 1))
 (.branch 8
 (.leaf (.quota 1))
 (.branch 9
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0272.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0272.rawLeaves 1 (RootedForests.RootedSubsumedForest0315.rawLeaves i) (routes.get i)

def disposition (j : Fin 10) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0272.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0272

/- Original module: RootedQuotaTransfer0272Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0272
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0272

/- Original module: RootedQuotaTransfer0272. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0272
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 10 :=
  routeInterval0

theorem disposition_checked (j : Fin 10) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0272.quota
      ((RootedForests.RootedSubsumedForest0315.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0272.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0272.rawLeaves 1 RootedForests.RootedSubsumedForest0272.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0272.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0315.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0272

/- Original module: RootedQuotaTransfer0290Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0290
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 290: use the complete forest for case 318, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0290.quota k ≤ RootedForests.RootedSubsumedForest0318.quota k := by
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
(.branch 10
 (.leaf (.quota 1))
 (.branch 15
 (.branch 12
 (.leaf (.quota 1))
 (.branch 13
 (.leaf (.quota 9))
 (.branch 14
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0290.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0290.rawLeaves 2 (RootedForests.RootedSubsumedForest0318.rawLeaves i) (routes.get i)

def disposition (j : Fin 21) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0290.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0290

/- Original module: RootedQuotaTransfer0290Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0290
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 21 :=
  interval_of_check test0 16 5 (by decide +kernel)

theorem test0_complete : Interval test0 0 21 :=
  (interval_append test0 0 16 21
  test0_block_0
  test0_block_1)
theorem routeInterval0 : Interval routeTest 0 21 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0290

/- Original module: RootedQuotaTransfer0290. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0290
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 21 :=
  routeInterval0

theorem disposition_checked (j : Fin 21) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0290.quota
      ((RootedForests.RootedSubsumedForest0318.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0290.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0290.rawLeaves 2 RootedForests.RootedSubsumedForest0290.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0290.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0318.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0290

/- Original module: RootedQuotaTransfer0312Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0312
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 312: use the complete forest for case 321, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0312.quota k ≤ RootedForests.RootedSubsumedForest0321.quota k := by
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
(.branch 68
 (.branch 34
 (.branch 17
 (.branch 8
 (.leaf (.quota 1))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 11
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 14
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 51
 (.branch 42
 (.leaf (.quota 1))
 (.branch 46
 (.leaf (.quota 1))
 (.branch 48
 (.branch 47
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 59
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 54
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 57
 (.leaf (.quota 1))
 (.branch 58
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 63
 (.branch 61
 (.branch 60
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 102
 (.branch 85
 (.branch 76
 (.branch 72
 (.leaf (.quota 1))
 (.branch 74
 (.branch 73
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 80
 (.leaf (.quota 1))
 (.branch 82
 (.branch 81
 (.leaf (.reuse 11))
 (.leaf (.reuse 12)))
 (.branch 83
 (.leaf (.reuse 13))
 (.branch 84
 (.leaf (.reuse 14))
 (.leaf (.quota 1)))))))
 (.branch 93
 (.leaf (.quota 1))
 (.branch 97
 (.leaf (.quota 1))
 (.branch 99
 (.branch 98
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 100
 (.leaf (.quota 2))
 (.branch 101
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 119
 (.branch 110
 (.branch 106
 (.branch 104
 (.branch 103
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 105
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 114
 (.leaf (.quota 1))
 (.branch 116
 (.leaf (.quota 1))
 (.branch 117
 (.leaf (.quota 1))
 (.branch 118
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 127
 (.leaf (.quota 1))
 (.branch 131
 (.branch 129
 (.leaf (.quota 1))
 (.branch 130
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 133
 (.branch 132
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0312.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0312.rawLeaves 24 (RootedForests.RootedSubsumedForest0321.rawLeaves i) (routes.get i)

def disposition (j : Fin 136) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0312.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0312

/- Original module: RootedQuotaTransfer0312Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0312
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0312

/- Original module: RootedQuotaTransfer0312Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0312
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 8 :=
  interval_of_check test128 0 8 (by decide +kernel)

theorem test128_complete : Interval test128 0 8 :=
  test128_block_0
theorem routeInterval128 : Interval routeTest 128 136 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0312

/- Original module: RootedQuotaTransfer0312. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0312
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 136 :=
  (interval_append routeTest 0 128 136
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 136) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0312.quota
      ((RootedForests.RootedSubsumedForest0321.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0312.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0312.rawLeaves 24 RootedForests.RootedSubsumedForest0312.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0312.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0321.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0312

/- Original module: RootedQuotaTransfer0356Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0356
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 356: use the complete forest for case 361, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0356.quota k ≤ RootedForests.RootedSubsumedForest0361.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0356.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0356.rawLeaves 1 (RootedForests.RootedSubsumedForest0361.rawLeaves i) (routes.get i)

def disposition (j : Fin 7) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0356.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0356

/- Original module: RootedQuotaTransfer0356Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0356
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0356

/- Original module: RootedQuotaTransfer0356. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0356
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 7 :=
  routeInterval0

theorem disposition_checked (j : Fin 7) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0356.quota
      ((RootedForests.RootedSubsumedForest0361.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0356.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0356.rawLeaves 1 RootedForests.RootedSubsumedForest0356.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0356.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0361.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0356

/- Original module: RootedQuotaTransfer0357Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0357
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 357: use the complete forest for case 361, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0357.quota k ≤ RootedForests.RootedSubsumedForest0361.quota k := by
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
(.branch 3
 (.branch 1
 (.leaf (.reuse 0))
 (.branch 2
 (.leaf (.reuse 1))
 (.leaf (.reuse 2))))
 (.branch 5
 (.branch 4
 (.leaf (.reuse 3))
 (.leaf (.reuse 4)))
 (.branch 6
 (.leaf (.reuse 5))
 (.leaf (.reuse 6)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0357.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0357.rawLeaves 7 (RootedForests.RootedSubsumedForest0361.rawLeaves i) (routes.get i)

def disposition (j : Fin 7) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0357.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0357

/- Original module: RootedQuotaTransfer0357Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0357
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0357

/- Original module: RootedQuotaTransfer0357. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0357
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 7 :=
  routeInterval0

theorem disposition_checked (j : Fin 7) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0357.quota
      ((RootedForests.RootedSubsumedForest0361.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0357.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0357.rawLeaves 7 RootedForests.RootedSubsumedForest0357.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0357.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0361.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0357

/- Original module: RootedQuotaTransfer0358Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0358
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 358: use the complete forest for case 361, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0358.quota k ≤ RootedForests.RootedSubsumedForest0361.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0358.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0358.rawLeaves 1 (RootedForests.RootedSubsumedForest0361.rawLeaves i) (routes.get i)

def disposition (j : Fin 7) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0358.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0358

/- Original module: RootedQuotaTransfer0358Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0358
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0358

/- Original module: RootedQuotaTransfer0358. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0358
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 7 :=
  routeInterval0

theorem disposition_checked (j : Fin 7) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0358.quota
      ((RootedForests.RootedSubsumedForest0361.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0358.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0358.rawLeaves 1 RootedForests.RootedSubsumedForest0358.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0358.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0361.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0358

/- Original module: RootedQuotaTransfer0359Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0359
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 359: use the complete forest for case 365, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0359.quota k ≤ RootedForests.RootedSubsumedForest0365.quota k := by
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
 (.leaf (.quota 1))
 (.branch 84
 (.leaf (.quota 1))
 (.branch 90
 (.branch 87
 (.leaf (.quota 1))
 (.branch 88
 (.leaf (.reuse 0))
 (.leaf (.quota 1))))
 (.branch 93
 (.leaf (.quota 1))
 (.branch 94
 (.leaf (.quota 1))
 (.branch 95
 (.leaf (.quota 1))
 (.leaf (.reuse 1)))))))))
 (.leaf (.quota 1)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0359.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0359.rawLeaves 2 (RootedForests.RootedSubsumedForest0365.rawLeaves i) (routes.get i)

def disposition (j : Fin 192) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0359.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0359

/- Original module: RootedQuotaTransfer0359Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0359
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0359
