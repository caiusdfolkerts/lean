module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0641Dispositions
public import RootedSubsumedForest0668Data
public import RootedSubsumedForest0642Dispositions
public import RootedSubsumedForest0669Data
public import RootedSubsumedForest0644Dispositions
public import RootedSubsumedForest0695Data
public import RootedSubsumedForest0645Dispositions
public import RootedSubsumedForest0696Data
public import RootedSubsumedForest0647Dispositions
public import RootedSubsumedForest0698Data
public import RootedSubsumedForest0649Dispositions
public import RootedSubsumedForest0681Data
public import RootedSubsumedForest0657Dispositions
public import RootedSubsumedForest0685Data
public import RootedSubsumedForest0658Dispositions
public import RootedSubsumedForest0686Data
public import RootedSubsumedForest0660Dispositions
public import RootedSubsumedForest0688Data
public import RootedSubsumedForest0662Dispositions
public import RootedSubsumedForest0704Data
public import RootedSubsumedForest0667Dispositions
public import RootedSubsumedForest0694Data
public import RootedSubsumedForest0671Dispositions
public import RootedSubsumedForest0672Dispositions
public import RootedSubsumedForest0674Dispositions
public import RootedSubsumedForest0676Dispositions
public import RootedSubsumedForest0706Data
public import RootedSubsumedForest0683Dispositions
public import RootedSubsumedForest0702Data
public import RootedSubsumedForest0690Dispositions
public import RootedSubsumedForest0700Dispositions
public import RootedSubsumedForest0709Dispositions
public import RootedSubsumedForest0713Data
public import RootedSubsumedForest0710Dispositions
public import RootedSubsumedForest0718Data
public import RootedSubsumedForest0711Dispositions
public import RootedSubsumedForest0721Data
public import RootedSubsumedForest0714Dispositions
public import RootedSubsumedForest0715Dispositions
public import RootedSubsumedForest0723Data
public import RootedSubsumedForest0716Dispositions

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0641Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0641
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 641: use the complete forest for case 668, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0641.quota k ≤ RootedForests.RootedSubsumedForest0668.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0641.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0641.rawLeaves 1 (RootedForests.RootedSubsumedForest0668.rawLeaves i) (routes.get i)

def disposition (j : Fin 7) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0641.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0641

/- Original module: RootedQuotaTransfer0641Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0641
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0641

/- Original module: RootedQuotaTransfer0641. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0641
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 7 :=
  routeInterval0

theorem disposition_checked (j : Fin 7) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0641.quota
      ((RootedForests.RootedSubsumedForest0668.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0641.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0641.rawLeaves 1 RootedForests.RootedSubsumedForest0641.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0641.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0668.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0641

/- Original module: RootedQuotaTransfer0642Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0642
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 642: use the complete forest for case 669, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0642.quota k ≤ RootedForests.RootedSubsumedForest0669.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0642.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0642.rawLeaves 1 (RootedForests.RootedSubsumedForest0669.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0642.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0642

/- Original module: RootedQuotaTransfer0642Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0642
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0642

/- Original module: RootedQuotaTransfer0642. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0642
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0642.quota
      ((RootedForests.RootedSubsumedForest0669.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0642.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0642.rawLeaves 1 RootedForests.RootedSubsumedForest0642.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0642.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0669.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0642

/- Original module: RootedQuotaTransfer0644Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0644
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 644: use the complete forest for case 695, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0644.quota k ≤ RootedForests.RootedSubsumedForest0695.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0644.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0644.rawLeaves 1 (RootedForests.RootedSubsumedForest0695.rawLeaves i) (routes.get i)

def disposition (j : Fin 138) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0644.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0644

/- Original module: RootedQuotaTransfer0644Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0644
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0644

/- Original module: RootedQuotaTransfer0644Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0644
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 10 :=
  interval_of_check test128 0 10 (by decide +kernel)

theorem test128_complete : Interval test128 0 10 :=
  test128_block_0
theorem routeInterval128 : Interval routeTest 128 138 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0644

/- Original module: RootedQuotaTransfer0644. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0644
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 138 :=
  (interval_append routeTest 0 128 138
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 138) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0644.quota
      ((RootedForests.RootedSubsumedForest0695.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0644.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0644.rawLeaves 1 RootedForests.RootedSubsumedForest0644.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0644.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0695.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0644

/- Original module: RootedQuotaTransfer0645Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0645
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 645: use the complete forest for case 696, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0645.quota k ≤ RootedForests.RootedSubsumedForest0696.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0645.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0645.rawLeaves 1 (RootedForests.RootedSubsumedForest0696.rawLeaves i) (routes.get i)

def disposition (j : Fin 15) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0645.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0645

/- Original module: RootedQuotaTransfer0645Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0645
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 15 :=
  interval_of_check test0 0 15 (by decide +kernel)

theorem test0_complete : Interval test0 0 15 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 15 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0645

/- Original module: RootedQuotaTransfer0645. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0645
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 15 :=
  routeInterval0

theorem disposition_checked (j : Fin 15) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0645.quota
      ((RootedForests.RootedSubsumedForest0696.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0645.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0645.rawLeaves 1 RootedForests.RootedSubsumedForest0645.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0645.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0696.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0645

/- Original module: RootedQuotaTransfer0647Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0647
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 647: use the complete forest for case 698, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0647.quota k ≤ RootedForests.RootedSubsumedForest0698.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0647.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0647.rawLeaves 1 (RootedForests.RootedSubsumedForest0698.rawLeaves i) (routes.get i)

def disposition (j : Fin 3) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0647.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0647

/- Original module: RootedQuotaTransfer0647Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0647
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0647

/- Original module: RootedQuotaTransfer0647. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0647
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 3 :=
  routeInterval0

theorem disposition_checked (j : Fin 3) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0647.quota
      ((RootedForests.RootedSubsumedForest0698.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0647.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0647.rawLeaves 1 RootedForests.RootedSubsumedForest0647.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0647.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0698.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0647

/- Original module: RootedQuotaTransfer0649Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0649
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 649: use the complete forest for case 681, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0649.quota k ≤ RootedForests.RootedSubsumedForest0681.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0649.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0649.rawLeaves 1 (RootedForests.RootedSubsumedForest0681.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0649.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0649

/- Original module: RootedQuotaTransfer0649Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0649
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0649

/- Original module: RootedQuotaTransfer0649. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0649
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0649.quota
      ((RootedForests.RootedSubsumedForest0681.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0649.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0649.rawLeaves 1 RootedForests.RootedSubsumedForest0649.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0649.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0681.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0649

/- Original module: RootedQuotaTransfer0657Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0657
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 657: use the complete forest for case 685, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0657.quota k ≤ RootedForests.RootedSubsumedForest0685.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0657.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0657.rawLeaves 1 (RootedForests.RootedSubsumedForest0685.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0657.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0657

/- Original module: RootedQuotaTransfer0657Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0657
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0657

/- Original module: RootedQuotaTransfer0657. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0657
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0657.quota
      ((RootedForests.RootedSubsumedForest0685.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0657.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0657.rawLeaves 1 RootedForests.RootedSubsumedForest0657.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0657.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0685.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0657

/- Original module: RootedQuotaTransfer0658Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0658
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 658: use the complete forest for case 686, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0658.quota k ≤ RootedForests.RootedSubsumedForest0686.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0658.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0658.rawLeaves 1 (RootedForests.RootedSubsumedForest0686.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0658.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0658

/- Original module: RootedQuotaTransfer0658Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0658
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0658

/- Original module: RootedQuotaTransfer0658. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0658
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0658.quota
      ((RootedForests.RootedSubsumedForest0686.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0658.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0658.rawLeaves 1 RootedForests.RootedSubsumedForest0658.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0658.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0686.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0658

/- Original module: RootedQuotaTransfer0660Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0660
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 660: use the complete forest for case 688, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0660.quota k ≤ RootedForests.RootedSubsumedForest0688.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0660.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0660.rawLeaves 1 (RootedForests.RootedSubsumedForest0688.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0660.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0660

/- Original module: RootedQuotaTransfer0660Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0660
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0660

/- Original module: RootedQuotaTransfer0660. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0660
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0660.quota
      ((RootedForests.RootedSubsumedForest0688.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0660.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0660.rawLeaves 1 RootedForests.RootedSubsumedForest0660.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0660.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0688.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0660

/- Original module: RootedQuotaTransfer0662Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0662
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 662: use the complete forest for case 704, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0662.quota k ≤ RootedForests.RootedSubsumedForest0704.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0662.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0662.rawLeaves 1 (RootedForests.RootedSubsumedForest0704.rawLeaves i) (routes.get i)

def disposition (j : Fin 10) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0662.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0662

/- Original module: RootedQuotaTransfer0662Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0662
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0662

/- Original module: RootedQuotaTransfer0662. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0662
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 10 :=
  routeInterval0

theorem disposition_checked (j : Fin 10) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0662.quota
      ((RootedForests.RootedSubsumedForest0704.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0662.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0662.rawLeaves 1 RootedForests.RootedSubsumedForest0662.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0662.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0704.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0662

/- Original module: RootedQuotaTransfer0667Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0667
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 667: use the complete forest for case 694, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0667.quota k ≤ RootedForests.RootedSubsumedForest0694.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0667.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0667.rawLeaves 1 (RootedForests.RootedSubsumedForest0694.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0667.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0667

/- Original module: RootedQuotaTransfer0667Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0667
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0667

/- Original module: RootedQuotaTransfer0667. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0667
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0667.quota
      ((RootedForests.RootedSubsumedForest0694.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0667.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0667.rawLeaves 1 RootedForests.RootedSubsumedForest0667.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0667.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0694.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0667

/- Original module: RootedQuotaTransfer0671Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0671
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 671: use the complete forest for case 695, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0671.quota k ≤ RootedForests.RootedSubsumedForest0695.quota k := by
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
(.branch 69
 (.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.leaf (.quota 1))
 (.branch 3
 (.leaf (.quota 1))
 (.leaf (.reuse 0))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 25
 (.branch 21
 (.branch 19
 (.leaf (.quota 1))
 (.branch 20
 (.leaf (.quota 1))
 (.leaf (.reuse 1))))
 (.branch 23
 (.leaf (.quota 1))
 (.branch 24
 (.leaf (.reuse 2))
 (.leaf (.quota 1)))))
 (.branch 29
 (.leaf (.quota 1))
 (.branch 31
 (.leaf (.quota 1))
 (.branch 32
 (.leaf (.quota 1))
 (.branch 33
 (.leaf (.reuse 3))
 (.leaf (.quota 1))))))))
 (.leaf (.quota 1)))
 (.branch 103
 (.branch 86
 (.branch 77
 (.leaf (.quota 1))
 (.branch 81
 (.leaf (.quota 1))
 (.branch 83
 (.leaf (.quota 1))
 (.branch 84
 (.leaf (.quota 1))
 (.branch 85
 (.leaf (.reuse 4))
 (.leaf (.quota 1)))))))
 (.branch 94
 (.leaf (.quota 1))
 (.branch 98
 (.leaf (.quota 1))
 (.branch 100
 (.leaf (.quota 1))
 (.branch 101
 (.leaf (.quota 1))
 (.branch 102
 (.leaf (.quota 1))
 (.leaf (.reuse 5))))))))
 (.leaf (.quota 1))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0671.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0671.rawLeaves 6 (RootedForests.RootedSubsumedForest0695.rawLeaves i) (routes.get i)

def disposition (j : Fin 138) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0671.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0671

/- Original module: RootedQuotaTransfer0671Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0671
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0671

/- Original module: RootedQuotaTransfer0671Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0671
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 10 :=
  interval_of_check test128 0 10 (by decide +kernel)

theorem test128_complete : Interval test128 0 10 :=
  test128_block_0
theorem routeInterval128 : Interval routeTest 128 138 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0671

/- Original module: RootedQuotaTransfer0671. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0671
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 138 :=
  (interval_append routeTest 0 128 138
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 138) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0671.quota
      ((RootedForests.RootedSubsumedForest0695.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0671.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0671.rawLeaves 6 RootedForests.RootedSubsumedForest0671.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0671.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0695.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0671

/- Original module: RootedQuotaTransfer0672Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0672
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 672: use the complete forest for case 696, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0672.quota k ≤ RootedForests.RootedSubsumedForest0696.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0672.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0672.rawLeaves 1 (RootedForests.RootedSubsumedForest0696.rawLeaves i) (routes.get i)

def disposition (j : Fin 15) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0672.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0672

/- Original module: RootedQuotaTransfer0672Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0672
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 15 :=
  interval_of_check test0 0 15 (by decide +kernel)

theorem test0_complete : Interval test0 0 15 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 15 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0672

/- Original module: RootedQuotaTransfer0672. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0672
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 15 :=
  routeInterval0

theorem disposition_checked (j : Fin 15) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0672.quota
      ((RootedForests.RootedSubsumedForest0696.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0672.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0672.rawLeaves 1 RootedForests.RootedSubsumedForest0672.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0672.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0696.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0672

/- Original module: RootedQuotaTransfer0674Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0674
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 674: use the complete forest for case 698, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0674.quota k ≤ RootedForests.RootedSubsumedForest0698.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0674.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0674.rawLeaves 1 (RootedForests.RootedSubsumedForest0698.rawLeaves i) (routes.get i)

def disposition (j : Fin 3) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0674.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0674

/- Original module: RootedQuotaTransfer0674Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0674
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0674

/- Original module: RootedQuotaTransfer0674. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0674
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 3 :=
  routeInterval0

theorem disposition_checked (j : Fin 3) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0674.quota
      ((RootedForests.RootedSubsumedForest0698.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0674.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0674.rawLeaves 1 RootedForests.RootedSubsumedForest0674.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0674.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0698.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0674

/- Original module: RootedQuotaTransfer0676Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0676
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 676: use the complete forest for case 706, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0676.quota k ≤ RootedForests.RootedSubsumedForest0706.quota k := by
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
(.branch 69
 (.leaf (.quota 1))
 (.branch 104
 (.branch 86
 (.leaf (.quota 1))
 (.branch 95
 (.branch 90
 (.branch 88
 (.branch 87
 (.leaf (.reuse 0))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 121
 (.leaf (.quota 1))
 (.branch 130
 (.branch 125
 (.branch 123
 (.branch 122
 (.leaf (.reuse 1))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0676.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0676.rawLeaves 2 (RootedForests.RootedSubsumedForest0706.rawLeaves i) (routes.get i)

def disposition (j : Fin 139) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0676.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0676

/- Original module: RootedQuotaTransfer0676Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0676
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0676

/- Original module: RootedQuotaTransfer0676Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0676
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 11 :=
  interval_of_check test128 0 11 (by decide +kernel)

theorem test128_complete : Interval test128 0 11 :=
  test128_block_0
theorem routeInterval128 : Interval routeTest 128 139 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0676

/- Original module: RootedQuotaTransfer0676. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0676
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 139 :=
  (interval_append routeTest 0 128 139
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 139) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0676.quota
      ((RootedForests.RootedSubsumedForest0706.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0676.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0676.rawLeaves 2 RootedForests.RootedSubsumedForest0676.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0676.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0706.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0676

/- Original module: RootedQuotaTransfer0683Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0683
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 683: use the complete forest for case 702, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0683.quota k ≤ RootedForests.RootedSubsumedForest0702.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0683.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0683.rawLeaves 1 (RootedForests.RootedSubsumedForest0702.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0683.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0683

/- Original module: RootedQuotaTransfer0683Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0683
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0683

/- Original module: RootedQuotaTransfer0683. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0683
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0683.quota
      ((RootedForests.RootedSubsumedForest0702.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0683.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0683.rawLeaves 1 RootedForests.RootedSubsumedForest0683.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0683.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0702.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0683

/- Original module: RootedQuotaTransfer0690Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0690
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 690: use the complete forest for case 704, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0690.quota k ≤ RootedForests.RootedSubsumedForest0704.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0690.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0690.rawLeaves 1 (RootedForests.RootedSubsumedForest0704.rawLeaves i) (routes.get i)

def disposition (j : Fin 10) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0690.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0690

/- Original module: RootedQuotaTransfer0690Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0690
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0690

/- Original module: RootedQuotaTransfer0690. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0690
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 10 :=
  routeInterval0

theorem disposition_checked (j : Fin 10) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0690.quota
      ((RootedForests.RootedSubsumedForest0704.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0690.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0690.rawLeaves 1 RootedForests.RootedSubsumedForest0690.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0690.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0704.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0690

/- Original module: RootedQuotaTransfer0700Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0700
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 700: use the complete forest for case 706, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0700.quota k ≤ RootedForests.RootedSubsumedForest0706.quota k := by
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
(.branch 69
 (.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.leaf (.quota 1))
 (.branch 3
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 6
 (.branch 5
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 7
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 25
 (.leaf (.quota 1))
 (.branch 29
 (.branch 27
 (.leaf (.quota 1))
 (.branch 28
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 31
 (.branch 30
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))
 (.branch 51
 (.branch 42
 (.leaf (.quota 1))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 54
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 64
 (.leaf (.quota 1))
 (.branch 66
 (.leaf (.quota 1))
 (.branch 67
 (.leaf (.quota 1))
 (.branch 68
 (.leaf (.quota 1))
 (.leaf (.reuse 8)))))))))
 (.branch 104
 (.branch 86
 (.branch 77
 (.branch 73
 (.branch 71
 (.leaf (.quota 1))
 (.branch 72
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 121
 (.leaf (.quota 1))
 (.branch 130
 (.branch 125
 (.leaf (.quota 1))
 (.branch 127
 (.branch 126
 (.leaf (.reuse 12))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 134
 (.leaf (.quota 1))
 (.branch 136
 (.leaf (.quota 1))
 (.branch 137
 (.leaf (.quota 1))
 (.branch 138
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0700.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0700.rawLeaves 14 (RootedForests.RootedSubsumedForest0706.rawLeaves i) (routes.get i)

def disposition (j : Fin 139) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0700.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0700

/- Original module: RootedQuotaTransfer0700Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0700
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0700

/- Original module: RootedQuotaTransfer0700Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0700
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 11 :=
  interval_of_check test128 0 11 (by decide +kernel)

theorem test128_complete : Interval test128 0 11 :=
  test128_block_0
theorem routeInterval128 : Interval routeTest 128 139 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0700

/- Original module: RootedQuotaTransfer0700. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0700
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 139 :=
  (interval_append routeTest 0 128 139
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 139) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0700.quota
      ((RootedForests.RootedSubsumedForest0706.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0700.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0700.rawLeaves 14 RootedForests.RootedSubsumedForest0700.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0700.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0706.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0700

/- Original module: RootedQuotaTransfer0709Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0709
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 709: use the complete forest for case 713, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0709.quota k ≤ RootedForests.RootedSubsumedForest0713.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0709.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0709.rawLeaves 1 (RootedForests.RootedSubsumedForest0713.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0709.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0709

/- Original module: RootedQuotaTransfer0709Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0709
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0709

/- Original module: RootedQuotaTransfer0709. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0709
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0709.quota
      ((RootedForests.RootedSubsumedForest0713.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0709.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0709.rawLeaves 1 RootedForests.RootedSubsumedForest0709.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0709.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0713.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0709

/- Original module: RootedQuotaTransfer0710Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0710
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 710: use the complete forest for case 718, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0710.quota k ≤ RootedForests.RootedSubsumedForest0718.quota k := by
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
 (.leaf (.quota 1))
 (.leaf (.reuse 0))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0710.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0710.rawLeaves 1 (RootedForests.RootedSubsumedForest0718.rawLeaves i) (routes.get i)

def disposition (j : Fin 10) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0710.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0710

/- Original module: RootedQuotaTransfer0710Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0710
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0710

/- Original module: RootedQuotaTransfer0710. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0710
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 10 :=
  routeInterval0

theorem disposition_checked (j : Fin 10) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0710.quota
      ((RootedForests.RootedSubsumedForest0718.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0710.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0710.rawLeaves 1 RootedForests.RootedSubsumedForest0710.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0710.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0718.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0710

/- Original module: RootedQuotaTransfer0711Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0711
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 711: use the complete forest for case 721, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0711.quota k ≤ RootedForests.RootedSubsumedForest0721.quota k := by
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
(.branch 90
 (.branch 45
 (.leaf (.quota 1))
 (.branch 67
 (.leaf (.quota 1))
 (.branch 78
 (.branch 72
 (.leaf (.quota 1))
 (.branch 75
 (.branch 73
 (.leaf (.quota 1))
 (.branch 74
 (.leaf (.quota 1))
 (.leaf (.reuse 0))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 135
 (.leaf (.quota 1))
 (.branch 157
 (.branch 146
 (.leaf (.quota 1))
 (.branch 151
 (.branch 148
 (.leaf (.quota 1))
 (.branch 149
 (.leaf (.quota 1))
 (.branch 150
 (.leaf (.reuse 1))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 168
 (.branch 162
 (.leaf (.quota 1))
 (.branch 165
 (.leaf (.quota 1))
 (.branch 166
 (.leaf (.quota 1))
 (.branch 167
 (.leaf (.reuse 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0711.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0711.rawLeaves 3 (RootedForests.RootedSubsumedForest0721.rawLeaves i) (routes.get i)

def disposition (j : Fin 180) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0711.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0711

/- Original module: RootedQuotaTransfer0711Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0711
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0711

/- Original module: RootedQuotaTransfer0711Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0711
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 32 :=
  interval_of_check test128 16 16 (by decide +kernel)

theorem test128_block_2 : Interval test128 32 48 :=
  interval_of_check test128 32 16 (by decide +kernel)

theorem test128_block_3 : Interval test128 48 52 :=
  interval_of_check test128 48 4 (by decide +kernel)

theorem test128_complete : Interval test128 0 52 :=
  (interval_append test128 0 32 52
  (interval_append test128 0 16 32
  test128_block_0
  test128_block_1)
  (interval_append test128 32 48 52
  test128_block_2
  test128_block_3))
theorem routeInterval128 : Interval routeTest 128 180 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0711

/- Original module: RootedQuotaTransfer0711. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0711
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 180 :=
  (interval_append routeTest 0 128 180
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 180) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0711.quota
      ((RootedForests.RootedSubsumedForest0721.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0711.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0711.rawLeaves 3 RootedForests.RootedSubsumedForest0711.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0711.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0721.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0711

/- Original module: RootedQuotaTransfer0714Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0714
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 714: use the complete forest for case 718, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0714.quota k ≤ RootedForests.RootedSubsumedForest0718.quota k := by
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
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0714.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0714.rawLeaves 1 (RootedForests.RootedSubsumedForest0718.rawLeaves i) (routes.get i)

def disposition (j : Fin 10) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0714.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0714

/- Original module: RootedQuotaTransfer0714Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0714
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0714

/- Original module: RootedQuotaTransfer0714. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0714
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 10 :=
  routeInterval0

theorem disposition_checked (j : Fin 10) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0714.quota
      ((RootedForests.RootedSubsumedForest0718.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0714.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0714.rawLeaves 1 RootedForests.RootedSubsumedForest0714.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0714.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0718.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0714

/- Original module: RootedQuotaTransfer0715Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0715
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 715: use the complete forest for case 723, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0715.quota k ≤ RootedForests.RootedSubsumedForest0723.quota k := by
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
  routeCheck RootedForests.RootedSubsumedForest0715.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0715.rawLeaves 1 (RootedForests.RootedSubsumedForest0723.rawLeaves i) (routes.get i)

def disposition (j : Fin 146) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0715.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0715

/- Original module: RootedQuotaTransfer0715Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0715
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0715

/- Original module: RootedQuotaTransfer0715Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0715
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 18 :=
  interval_of_check test128 16 2 (by decide +kernel)

theorem test128_complete : Interval test128 0 18 :=
  (interval_append test128 0 16 18
  test128_block_0
  test128_block_1)
theorem routeInterval128 : Interval routeTest 128 146 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0715

/- Original module: RootedQuotaTransfer0715. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0715
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 146 :=
  (interval_append routeTest 0 128 146
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 146) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0715.quota
      ((RootedForests.RootedSubsumedForest0723.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0715.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0715.rawLeaves 1 RootedForests.RootedSubsumedForest0715.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0715.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0723.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0715

/- Original module: RootedQuotaTransfer0716Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0716
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 716: use the complete forest for case 721, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0716.quota k ≤ RootedForests.RootedSubsumedForest0721.quota k := by
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
(.branch 90
 (.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.leaf (.quota 1))
 (.branch 8
 (.leaf (.quota 1))
 (.branch 9
 (.leaf (.quota 1))
 (.branch 10
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.leaf (.quota 1)))
 (.branch 33
 (.leaf (.quota 1))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf (.quota 2))
 (.branch 35
 (.leaf (.quota 1))
 (.leaf (.reuse 2))))
 (.leaf (.quota 1)))
 (.branch 42
 (.branch 40
 (.leaf (.quota 1))
 (.branch 41
 (.leaf (.reuse 3))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 67
 (.leaf (.quota 1))
 (.branch 78
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf (.reuse 4))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 75
 (.leaf (.quota 1))
 (.branch 76
 (.leaf (.reuse 6))
 (.branch 77
 (.leaf (.reuse 7))
 (.leaf (.quota 1))))))
 (.branch 84
 (.branch 81
 (.leaf (.quota 1))
 (.branch 82
 (.leaf (.reuse 8))
 (.branch 83
 (.leaf (.reuse 9))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 93
 (.leaf (.quota 1))
 (.branch 94
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1)))
 (.branch 106
 (.leaf (.quota 1))
 (.branch 109
 (.branch 107
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 123
 (.branch 117
 (.branch 114
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 120
 (.branch 118
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 157
 (.branch 146
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf (.quota 1))
 (.leaf (.reuse 17)))
 (.branch 138
 (.leaf (.reuse 18))
 (.leaf (.quota 1))))
 (.branch 143
 (.leaf (.quota 1))
 (.branch 144
 (.leaf (.quota 1))
 (.branch 145
 (.leaf (.quota 2))
 (.leaf (.reuse 20))))))
 (.branch 151
 (.branch 148
 (.leaf (.quota 1))
 (.branch 149
 (.leaf (.quota 1))
 (.branch 150
 (.leaf (.quota 1))
 (.leaf (.reuse 22)))))
 (.branch 154
 (.leaf (.quota 1))
 (.branch 155
 (.leaf (.quota 1))
 (.branch 156
 (.leaf (.reuse 23))
 (.leaf (.quota 1)))))))
 (.branch 168
 (.leaf (.quota 1))
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf (.reuse 25))
 (.leaf (.quota 1)))
 (.branch 172
 (.leaf (.quota 1))
 (.branch 173
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 177
 (.branch 175
 (.leaf (.quota 1))
 (.branch 176
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 178
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0716.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0716.rawLeaves 30 (RootedForests.RootedSubsumedForest0721.rawLeaves i) (routes.get i)

def disposition (j : Fin 180) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0716.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0716
